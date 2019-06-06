/*
    This file is part of the clazy static checker.

    Copyright (C) 2019 Klarälvdalens Datakonsult AB, a KDAB Group company, info@kdab.com
    Author: Sérgio Martins <sergio.martins@kdab.com>

    This library is free software; you can redistribute it and/or
    modify it under the terms of the GNU Library General Public
    License as published by the Free Software Foundation; either
    version 2 of the License, or (at your option) any later version.

    This library is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    Library General Public License for more details.

    You should have received a copy of the GNU Library General Public License
    along with this library; see the file COPYING.LIB.  If not, write to
    the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
    Boston, MA 02110-1301, USA.
*/

#include "MiniAstDumper.h"
#include "SourceCompatibilityHelpers.h"
#include "AccessSpecifierManager.h"
#include "clazy_stl.h"
#include "FunctionUtils.h"
#include "QtUtils.h"
#include "StringUtils.h"
#include <clang/Frontend/CompilerInstance.h>
#include <clang/Frontend/FrontendPluginRegistry.h>

#include <fstream>
#include <unistd.h>
#include <limits.h>

using namespace clang;
using namespace std;

static bool s_debugSeen = false;
static bool s_debugSkipping = false;

enum ClassFlag {
    ClassFlag_None = 0,
    ClassFlag_QObject = 1
};

enum MethodFlag {
    MethodFlag_None = 0,
    MethodFlag_Signal = 1,
    MethodFlag_Constructor = 2,
    MethodFlag_DefaultConstructor = 4,
    MethodFlag_CopyConstructor = 8,
    MethodFlag_MoveConstructor = 16,
    MethodFlag_Destructor = 32,
    MethodFlag_CopyAssignOperator = 64,
    MethodFlag_MoveAssignOperator = 128
};

enum StuffType {
    StuffType_FunctionDecl = 1, ///< excluding methods
    StuffType_MethodDecl = 2,
    StuffType_RecordDecl = 4,
    StuffType_CallExpr = 8
};

MiniAstDumperASTAction::MiniAstDumperASTAction()
{
}

bool MiniAstDumperASTAction::ParseArgs(const CompilerInstance &, const std::vector<string> &)
{
    return true;
}

std::unique_ptr<ASTConsumer> MiniAstDumperASTAction::CreateASTConsumer(CompilerInstance &ci, llvm::StringRef)
{
    return std::unique_ptr<MiniASTDumperConsumer>(new MiniASTDumperConsumer(ci));
}

MiniASTDumperConsumer::MiniASTDumperConsumer(CompilerInstance &ci)
    : m_ci(ci)
    , m_accessSpecifierManager(new AccessSpecifierManager(ci))
{
    auto &sm = m_ci.getASTContext().getSourceManager();
    const FileEntry *fileEntry = sm.getFileEntryForID(sm.getMainFileID());
    m_currentCppFile = fileEntry->getName();

    m_cborBuf = reinterpret_cast<uint8_t*>(malloc(m_bufferSize));

    cbor_encoder_init(&m_cborEncoder, m_cborBuf, m_bufferSize, 0);
    cborCreateMap(&m_cborEncoder, &m_cborRootMapEncoder, 4);
    cborEncodeString(m_cborRootMapEncoder, "tu");
    cborEncodeString(m_cborRootMapEncoder, m_currentCppFile.c_str());

    char cwd[4096]; // TODO: Just use std::filesystem::current_path
    cborEncodeString(m_cborRootMapEncoder, "cwd");
    cborEncodeString(m_cborRootMapEncoder, std::string(getcwd(cwd, sizeof(cwd))).c_str());

    cborEncodeString(m_cborRootMapEncoder, "stuff");
    cborCreateArray(&m_cborRootMapEncoder, &m_cborStuffArray, CborIndefiniteLength);
}

MiniASTDumperConsumer::~MiniASTDumperConsumer()
{
    cborCloseContainer(&m_cborRootMapEncoder, &m_cborStuffArray);

    cborEncodeString(m_cborRootMapEncoder, "files");
    dumpFileMap(&m_cborRootMapEncoder);

    cborCloseContainer(&m_cborEncoder, &m_cborRootMapEncoder);


    size_t size = cbor_encoder_get_buffer_size(&m_cborEncoder, m_cborBuf);

    const std::string cborFileName = m_currentCppFile + ".cbor";

    std::ofstream myFile(cborFileName, std::ios::out | ios::binary);
    myFile.write(reinterpret_cast<char*>(m_cborBuf), long(size));
    delete m_cborBuf;
}

bool MiniASTDumperConsumer::VisitDecl(Decl *decl)
{
    m_accessSpecifierManager->VisitDeclaration(decl);

    if (s_debugSeen)
        llvm::errs() << "Seen decl: " << decl
                     << "; id= " << int64_t(decl)
                     << " ; " << decl->getDeclKindName() << "\n";

    if (auto tsd = dyn_cast<ClassTemplateSpecializationDecl>(decl)) {
        dumpCXXRecordDecl(tsd, &m_cborStuffArray);
    } else if (auto rec = dyn_cast<CXXRecordDecl>(decl)) {
        if (!rec->isThisDeclarationADefinition()) {
            // No forward-declarations
            if (s_debugSkipping)
                llvm::errs() << "Skipping forward-decl rec=" << rec << " ; " << rec->getQualifiedNameAsString() << "; "
                             << clazy::getLocStart(rec).printToString(m_ci.getSourceManager()) << "\n";
            return true;
        }

        dumpCXXRecordDecl(rec, &m_cborStuffArray);
    } else if (auto ctd = dyn_cast<ClassTemplateDecl>(decl)) {
        for (auto s : ctd->specializations())
            dumpCXXRecordDecl(s, &m_cborStuffArray);
    } else if (auto method = dyn_cast<CXXMethodDecl>(decl)) {
        if (alreadySeen(method))
            return true;

        auto methodDecl = dyn_cast<CXXMethodDecl>(clazy::getFunctionDeclaration(method));
        if (alreadySeen(method))
            return true;

        CXXRecordDecl *classDecl = methodDecl->getParent();
        if (!alreadySeen(classDecl))
            dumpCXXRecordDecl(classDecl, &m_cborStuffArray);

        dumpCXXMethodDecl(methodDecl, &m_cborStuffArray, true);
    } else if (auto func = dyn_cast<FunctionDecl>(decl)) {
        if (func->getTemplatedKind() == FunctionDecl::TK_FunctionTemplate) {
            // Already handled when catching FunctionTemplateDecl. When we write func->getTemplatedDecl().
            return true;
        }

        dumpFunctionDecl(func, &m_cborStuffArray);
    } else if (auto func = dyn_cast<FunctionTemplateDecl>(decl)) {

        dumpFunctionDecl(func->getTemplatedDecl(), &m_cborStuffArray);

        for (auto s : func->specializations()) {
            dumpFunctionDecl(s, &m_cborStuffArray);
        }
    }

    return true;
}

bool MiniASTDumperConsumer::VisitStmt(Stmt *stmt)
{
    if (auto callExpr = dyn_cast<CallExpr>(stmt)) {
        dumpCallExpr(callExpr, &m_cborStuffArray);
    }

    return true;
}

void MiniASTDumperConsumer::HandleTranslationUnit(ASTContext &ctx)
{
    TraverseDecl(ctx.getTranslationUnitDecl());
}

void MiniASTDumperConsumer::dumpCXXMethodDecl(CXXMethodDecl *method, CborEncoder *encoder, bool printType)
{
    if (alreadySeen(method))
        return;

    m_seenFunctions.insert(method);

    CborEncoder methodMap;
    cborCreateMap(encoder, &methodMap, CborIndefiniteLength);

    cborEncodeString(methodMap, "name");
    cborEncodeString(methodMap, method->getQualifiedNameAsString().c_str());

    cborEncodeString(methodMap, "local_id");
    cborEncodeInt(methodMap, int64_t(method));

    if (printType) {
        cborEncodeString(methodMap, "type");
        cborEncodeInt(methodMap, StuffType_MethodDecl);

        cborEncodeString(methodMap, "class_local_id");
        cborEncodeInt(methodMap, int64_t(method->getParent()));
    }

    int64_t flags = 0;

    if (m_accessSpecifierManager->qtAccessSpecifierType(method) == QtAccessSpecifier_Signal)
        flags |= MethodFlag_Signal;

    if (isa<CXXDestructorDecl>(method))
        flags |= MethodFlag_Destructor;
    if (auto ctor = dyn_cast<CXXConstructorDecl>(method)) {
        flags |= MethodFlag_Constructor;

        if (ctor->isCopyConstructor())
            flags |= MethodFlag_CopyConstructor;

        if (ctor->isMoveConstructor())
            flags |= MethodFlag_MoveConstructor;

        if (ctor->isDefaultConstructor())
            flags |= MethodFlag_DefaultConstructor;
    }

    if (method->isCopyAssignmentOperator())
        flags |= MethodFlag_CopyAssignOperator;

    if (method->isMoveAssignmentOperator())
        flags |= MethodFlag_MoveAssignOperator;

    if (flags) {
        cborEncodeString(methodMap, "method_flags");
        cborEncodeInt(methodMap, flags);
    }

    cborEncodeString(methodMap, "loc");
    const SourceLocation loc = clazy::getLocStart(method);
    dumpLocation(loc, &methodMap);

    cborCloseContainer(encoder, &methodMap);


    //if (method->getQualifiedNameAsString() == "QString::QString") {
       /* llvm::errs() << "registering method! local_id=" << int64_t(method)
                     << "; " << method->getQualifiedNameAsString()
                     << "; " << method->getBeginLoc().printToString(m_ci.getSourceManager())
                     << "; printType=" << printType
                     << "; parent=" << method->getParent()
                     << "; parentLoc= " << clazy::getLocStart(method->getParent()).printToString(m_ci.getSourceManager())
                     << "; flags=" << flags
                     << "; " << method->getTemplateSpecializationInfo()
                     << "\n";*/
    //}

}

void MiniASTDumperConsumer::dumpFunctionDecl(FunctionDecl *func, CborEncoder *encoder)
{
    if (alreadySeen(func))
        return;

    m_seenFunctions.insert(func);
/*
    if (func->getQualifiedNameAsString() == "qMin") {
        llvm::errs() << "registering! " << func << " ; " << func->getQualifiedNameAsString()
                     << "; " << func->getBeginLoc().printToString(m_ci.getSourceManager())
                     << "; isTemplateInstantiation=" << func->isTemplateInstantiation()
                     << "; isTemplateDecl=" << func->isTemplateDecl()
                     << "; isTemplated=" << func->isTemplated()
                     << "; specializationInfo=" << func->getTemplateSpecializationInfo()
                     << "\n";
        //func->dump();

    }*/

    std::string templateArgsStr;
    if (func->isTemplateInstantiation()) {

        const auto &args = func->getTemplateSpecializationArgs();
        const size_t count = args->size();
        for (size_t i = 0; i < count; ++i) {
            TemplateArgument arg = args->get(i);

            if (arg.getKind() == TemplateArgument::Type) {
                // TODO: Use clang::printTemplateArgumentList instead
                QualType qt = arg.getAsType();
                if (qt.isNull()) {
                    llvm::errs() << "null type for " << func->getQualifiedNameAsString() << "\n";
                } else {
                    templateArgsStr += qt.getAsString();
                    if (i != count-1)
                        templateArgsStr += ", ";
                }
            }
        }
    }

    CborEncoder recordMap;
    cborCreateMap(encoder, &recordMap, CborIndefiniteLength);

    cborEncodeString(recordMap, "name");
    cborEncodeString(recordMap, func->getQualifiedNameAsString().c_str());

    cborEncodeString(recordMap, "type");
    cborEncodeInt(recordMap, StuffType_FunctionDecl);

    cborEncodeString(recordMap, "local_id");
    cborEncodeInt(recordMap, int64_t(func));

    cborEncodeString(recordMap, "loc");
    const SourceLocation loc = clazy::getLocStart(func);
    dumpLocation(loc, &recordMap);

    if (auto spec = func->getTemplateSpecializationInfo()) {
        // This is a function template specialization, so also dump the specialization location
        // Otherwise, for example, qMin<int> and qMin<long> will have the same hash, since they have the same source location
        SourceLocation specializationLoc = spec->getPointOfInstantiation();
        if (specializationLoc.isValid()) {
            cborEncodeString(recordMap, "specialization_loc");
            dumpLocation(specializationLoc, &recordMap);
        }
    }

    if (!templateArgsStr.empty()) {
        cborEncodeString(recordMap, "template_args");
        cborEncodeString(recordMap, templateArgsStr.c_str());
    }

    cborCloseContainer(encoder, &recordMap);
}

void MiniASTDumperConsumer::dumpCXXRecordDecl(CXXRecordDecl *rec, CborEncoder *encoder)
{
    if (alreadySeen(rec))
        return;

    m_seenClasses.insert(rec);

    std::string templateArgsStr;
    if (auto specialization = dyn_cast<ClassTemplateSpecializationDecl>(rec)) {
        auto &args = specialization->getTemplateArgs();
        const size_t count = args.size();
        for (size_t i = 0; i < count; ++i) {
            TemplateArgument arg = args.get(i);

            if (arg.getKind() == TemplateArgument::Type) {
                // TODO: Use clang::printTemplateArgumentList instead
                QualType qt = arg.getAsType();
                if (qt.isNull()) {
                    llvm::errs() << "null type for " << rec->getQualifiedNameAsString() << "\n";
                } else {
                    templateArgsStr += qt.getAsString();
                    if (i != count-1)
                        templateArgsStr += ", ";
                }
            }
        }
    }

    /*llvm::errs() << "dumpCXXRecordDecl=" << rec->getQualifiedNameAsString()
                 << "; local_id=" << int64_t(rec)
                 << "; template args=" << templateArgsStr
                 << "\n";*/

    CborEncoder recordMap;
    cborCreateMap(encoder, &recordMap, CborIndefiniteLength);

    cborEncodeString(recordMap, "local_id");
    cborEncodeInt(recordMap, int64_t(rec));

    cborEncodeString(recordMap, "type");
    cborEncodeInt(recordMap, StuffType_RecordDecl);

    std::string qualified_name = rec->getQualifiedNameAsString().c_str();
    if (qualified_name.empty()) {
        qualified_name = "anonymous";
    }

    cborEncodeString(recordMap, "name");
    cborEncodeString(recordMap, qualified_name.c_str());

    cborEncodeString(recordMap, "loc");
    const SourceLocation loc = clazy::getLocStart(rec);
    dumpLocation(loc, &recordMap);

    if (!templateArgsStr.empty()) {
        cborEncodeString(recordMap, "template_args");
        cborEncodeString(recordMap, templateArgsStr.c_str());
    }

    int64_t flags = 0;

    if (clazy::isQObject(rec))
        flags |= ClassFlag_QObject;

    if (flags) {
        cborEncodeString(recordMap, "class_flags");
        cborEncodeInt(recordMap, flags);
    }

    cborEncodeString(recordMap, "methods");
    CborEncoder cborMethodList;
    cborCreateArray(&recordMap, &cborMethodList, CborIndefiniteLength);
    for (auto method : rec->methods()) {
        dumpCXXMethodDecl(method, &cborMethodList);
    }

    cborCloseContainer(&recordMap, &cborMethodList);
    cborCloseContainer(&m_cborStuffArray, &recordMap);
}

void MiniASTDumperConsumer::dumpCallExpr(CallExpr *callExpr, CborEncoder *encoder)
{
    FunctionDecl *func = callExpr->getDirectCallee();
    if (!func || !func->getDeclName().isIdentifier())
        return;

    const bool isBuiltin = func->getBuiltinID() != 0;
    if (isBuiltin) //We don't need them now
        return;

    auto method = dyn_cast<CXXMethodDecl>(func);
    if (method) {

        if (!alreadySeen(method)) {
            // Some weird stuff related to templates isnt being registered, add them manually:
            if (!alreadySeen(method->getParent()))
                dumpCXXRecordDecl(method->getParent(), &m_cborStuffArray);
            if (!alreadySeen(method))
                dumpCXXMethodDecl(method, &m_cborStuffArray);
        }

        // For methods we store the declaration
        func = clazy::getFunctionDeclaration(method);
    }

    /*llvm::errs() << "Dumping call to " << func->getQualifiedNameAsString()
                 << "; func_loc=" << clazy::getLocStart(func).printToString(m_ci.getSourceManager())
                 << " ; id=" << int64_t(func) << "\n";*/


    if (func->getQualifiedNameAsString() == "KDDockWidgets::Anchor::toChanged") {
        llvm::errs() << "found call to "
                     << func
                     << "; " << func->getQualifiedNameAsString()
                     << "; original=" << callExpr->getDirectCallee()
                     << "; funcloc " << func->getBeginLoc().printToString(m_ci.getSourceManager())
                     << "; original-loc= " << callExpr->getDirectCallee()->getBeginLoc().printToString(m_ci.getSourceManager())

                     << "; " << func->getTemplatedKind() << " ; " << callExpr->getDirectCallee()->getTemplatedKind()
                     << "; localId=" << int64_t(func)
                     << "\n";
    }

    CborEncoder callMap;
    cborCreateMap(encoder, &callMap, 3);

    cborEncodeString(callMap, "type");
    cborEncodeInt(callMap, StuffType_CallExpr);

    cborEncodeString(callMap, "callee_local_id");
    cborEncodeInt(callMap, int64_t(func));

    cborEncodeString(callMap, "loc");
    dumpLocation(clazy::getLocStart(callExpr), &callMap);

    cborCloseContainer(encoder, &callMap);
}

void MiniASTDumperConsumer::dumpLocation(SourceLocation loc, CborEncoder *encoder)
{
    if (!loc.isValid()) {
        llvm::errs() << "dumpLocation: Invalid location!\n";
        return;
    }

    CborEncoder locMap;
    cborCreateMap(encoder, &locMap, CborIndefiniteLength);

    auto &sm = m_ci.getSourceManager();

    if (loc.isMacroID()) {
        /// The place where the macro is defined:
        SourceLocation spellingLoc = sm.getSpellingLoc(loc);
        const FileID fileId = sm.getFileID(spellingLoc);
        m_fileIds[fileId.getHashValue()] = sm.getFilename(spellingLoc).str();

        cborEncodeString(locMap, "spellingFileId");
        cborEncodeInt(locMap, fileId.getHashValue());

        cborEncodeString(locMap, "spellingLine");
        cborEncodeInt(locMap, sm.getSpellingLineNumber(loc));

        cborEncodeString(locMap, "spellingColumn");
        cborEncodeInt(locMap, sm.getSpellingColumnNumber(loc));

        /// Get the place where the macro is used:
        loc = sm.getExpansionLoc(loc);
    }

    const FileID fileId = sm.getFileID(loc);
    m_fileIds[fileId.getHashValue()] = sm.getFilename(loc).str();

    if (sm.getFilename(loc).empty()) {
        // Shouldn't happen
        llvm::errs() << "Invalid filename for " << loc.printToString(sm) <<  "\n";
    }

    cborEncodeString(locMap, "fileId");
    cborEncodeInt(locMap, fileId.getHashValue());

    auto ploc = sm.getPresumedLoc(loc);
    cborEncodeString(locMap, "line");

    cborEncodeInt(locMap,  ploc.getLine());
    cborEncodeString(locMap, "column");
    cborEncodeInt(locMap,  ploc.getColumn());

    cborCloseContainer(encoder, &locMap);
}

void MiniASTDumperConsumer::dumpFileMap(CborEncoder *encoder)
{
    CborEncoder fileMap;
    cborCreateMap(encoder, &fileMap, m_fileIds.size());

    for (auto it : m_fileIds) {
        cborEncodeString(fileMap, std::to_string(it.first).c_str());
        cborEncodeString(fileMap, it.second.c_str());
    }

    cborCloseContainer(encoder, &fileMap);
}

void MiniASTDumperConsumer::cborEncodeString(CborEncoder &enc, const char *str)
{
    if (cbor_encode_text_stringz(&enc, str) != CborNoError)
        llvm::errs() << "cborEncodeString error\n";
}

void MiniASTDumperConsumer::cborEncodeInt(CborEncoder &enc, int64_t v)
{
    if (cbor_encode_int(&enc, v) != CborNoError)
        llvm::errs() << "cborEncodeInt error\n";
}

void MiniASTDumperConsumer::cborEncodeBool(CborEncoder &enc, bool b)
{
    if (cbor_encode_boolean(&enc, b) != CborNoError)
        llvm::errs() << "cborEncodeBool error\n";
}

void MiniASTDumperConsumer::cborCreateMap(CborEncoder *encoder, CborEncoder *mapEncoder, size_t length)
{
    if (cbor_encoder_create_map(encoder, mapEncoder, length) != CborNoError)
        llvm::errs() << "cborCreateMap error\n";
}

void MiniASTDumperConsumer::cborCreateArray(CborEncoder *encoder, CborEncoder *arrayEncoder, size_t length)
{
    if (cbor_encoder_create_array(encoder, arrayEncoder, length) != CborNoError)
        llvm::errs() << "cborCreateMap error\n";
}

void MiniASTDumperConsumer::cborCloseContainer(CborEncoder *encoder, const CborEncoder *containerEncoder)
{
    if (cbor_encoder_close_container(encoder, containerEncoder) != CborNoError)
        llvm::errs() << "cborCloseContainer error\n";
}

bool MiniASTDumperConsumer::alreadySeen(const FunctionDecl *func) const
{
    return !func || m_seenFunctions.find(func) != m_seenFunctions.cend();
}

bool MiniASTDumperConsumer::alreadySeen(const CXXRecordDecl *record) const
{
    return !record || m_seenClasses.find(record) != m_seenClasses.cend();
}

static FrontendPluginRegistry::Add<MiniAstDumperASTAction>
X2("clazyMiniAstDumper", "Clazy Mini AST Dumper plugin");
