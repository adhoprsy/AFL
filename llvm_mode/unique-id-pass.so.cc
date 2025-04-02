#include <llvm-15/llvm/IR/Value.h>
#include <llvm-15/llvm/Support/raw_ostream.h>
#define UNIQUE_ID_PASS
#define AFL_LLVM_PASS
#include "../config.h"
#include "../debug.h"
#include "../xxhash.h"

#include <random>
#include <unordered_map>
#include <unordered_set>
#include <stdio.h>
#include <stdlib.h>
#include <thread>
#include <unistd.h>
#include <chrono>

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Constant.h"

#if LLVM_VERSION_MAJOR >= 14
  #include "llvm/Passes/PassPlugin.h"
  #include "llvm/Passes/PassBuilder.h"
  #include "llvm/IR/PassManager.h"
  #include "llvm/Passes/OptimizationLevel.h"
#else
  #include "llvm/IR/LegacyPassManager.h"
#endif

#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

using namespace llvm;

#if LLVM_VERSION_MAJOR <= 11
namespace {

class UniqueID : public ModulePass {

public:
  static char ID;
  std::unordered_map<uint64_t, std::unordered_set<uint64_t>> childs_map;

  UniqueID() : ModulePass(ID) {}

  bool runOnModule(Module &M) override;

  // StringRef getPassName() const override {
  //  return "American Fuzzy Lop Instrumentation";
  // }
};
#else

class UniqueID : public PassInfoMixin<UniqueID> {
  public:

  std::unordered_map<uint64_t, std::unordered_set<uint64_t>> childs_map;

  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
  static bool isRequired() { return true; }
};

PassPluginLibraryInfo getUniqueIDPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "UniqueIDPass", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerOptimizerLastEPCallback(
                [](ModulePassManager &MPM, OptimizationLevel Level) {
                  MPM.addPass(UniqueID());
                });
          }};
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return getUniqueIDPluginInfo();
}
#endif

#if LLVM_VERSION_MAJOR <= 11
} // namespace
char UniqueID::ID = 0;
#endif

uint64_t read_id_from_metadata(MDNode* MD) {
  if (MD && MD->getNumOperands() >= 1) {
    if (ConstantInt *CI = mdconst::dyn_extract<ConstantInt>(MD->getOperand(0))) {
      uint64_t id = CI->getZExtValue();
      return id;
    }
  }
  return 0;
}

#if LLVM_VERSION_MAJOR <= 11
bool UniqueID::runOnModule(Module &M) {
#else

std::string get_function_filename(const Function &F) {
    if (DISubprogram *SP = F.getSubprogram()) {
        if (DIFile *File = SP->getFile()) {
            return File->getFilename().str();
        }
    }
    return "";
}

uint64_t generate_bb_hash(const BasicBlock* BB) {
  std::string BBContent;
  raw_string_ostream os(BBContent);
  for (const auto& I : *BB) {
    os<<I.getOpcode()<<" ";
    for (const Value *Op : I.operands()) {
        if (Op->getType()) {
          Op->getType()->print(os);
          os << " ";
        }
    }
  }
  // function name
  os << BB->getParent()->getName();
  // errs() << BB->getParent()->getName() << " / ";

  // file name
  os << get_function_filename(*BB->getParent());
  // errs() << get_function_filename(*BB->getParent()) << "\n";

  std::hash<std::string> hasher;
  return hasher(os.str()) % MAP_SIZE;
}

PreservedAnalyses UniqueID::run(Module &M, ModuleAnalysisManager &AM) {

#endif

  // unsigned random_seed =
  //   std::chrono::system_clock::now().time_since_epoch().count()
  //   ^ std::hash<std::thread::id>()(std::this_thread::get_id());
  // std::mt19937 gen(random_seed);
  // std::uniform_int_distribution<int> distr(0, MAP_SIZE);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "unique-id-pass " cBRI VERSION cRST " by <sjj>\n");

  } else
    be_quiet = 1;

  /* Instrument all the things! */

  int inst_blocks = 0;

  for (auto &F : M)
    for (auto &BB : F) {
      Instruction* terminator = BB.getTerminator();
      if (!terminator) continue;

      // branch instructions
      const BranchInst* br = dyn_cast<BranchInst>(terminator);
      if (br && br->isConditional()) {

        auto IP = BB.getFirstInsertionPt();
        IRBuilder<> IRB(&(*IP));

        if (!terminator->hasMetadata(M.getMDKindID("basicblock.id"))) {
          // uint64_t raw_id = distr(gen);
          errs() << *terminator << "\n";
          uint64_t raw_id = generate_bb_hash(&BB);
          MDNode* node =  MDNode::get(BB.getContext(), ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(BB.getContext()), raw_id)));
          terminator->setMetadata(M.getMDKindID("basicblock.id"), node);
          inst_blocks++;
        }

        uint64_t parent_id =read_id_from_metadata(terminator->getMetadata(M.getMDKindID("basicblock.id")));

        // assign id for its child
        for (BasicBlock* succ: successors(&BB)) {
          Instruction* term = succ->getTerminator();
          if (!term) continue;
          auto IP = succ->getFirstInsertionPt();
          IRBuilder<> IRB(&(*IP));
          if (!term->hasMetadata(M.getMDKindID("basicblock.id"))) {
            // uint64_t raw_id = distr(gen);
            errs() << *term << "\n";
            uint64_t raw_id = generate_bb_hash(succ);

            childs_map[parent_id].insert(raw_id);

            MDNode* node =  MDNode::get(BB.getContext(), ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(BB.getContext()), raw_id)));
            term->setMetadata(M.getMDKindID("basicblock.id"), node);
            inst_blocks++;
          }
          else {
            uint64_t child_id =read_id_from_metadata(term->getMetadata(M.getMDKindID("basicblock.id")));
            childs_map[parent_id].insert(child_id);
          }
        }
      }

      // switch instructions
      const SwitchInst* sw = dyn_cast<SwitchInst>(terminator);
      if (sw) {
        auto IP = BB.getFirstInsertionPt();
        IRBuilder<> IRB(&(*IP));

        if (!terminator->hasMetadata(M.getMDKindID("basicblock.id"))) {
          // uint64_t raw_id = distr(gen);
          uint64_t raw_id = generate_bb_hash(&BB);
          MDNode* node =  MDNode::get(BB.getContext(), ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(BB.getContext()), raw_id)));
          terminator->setMetadata(M.getMDKindID("basicblock.id"), node);
          inst_blocks++;
        }
        uint64_t parent_id =read_id_from_metadata(terminator->getMetadata(M.getMDKindID("basicblock.id")));
        // assign id for its child
        for (BasicBlock* succ: successors(&BB)) {
          Instruction* term = succ->getTerminator();
          if (!term) continue;
          auto IP = succ->getFirstInsertionPt();
          IRBuilder<> IRB(&(*IP));
          if (!term->hasMetadata(M.getMDKindID("basicblock.id"))) {
            // uint64_t raw_id = distr(gen);
            uint64_t raw_id = generate_bb_hash(succ);
            childs_map[parent_id].insert(raw_id);
            MDNode* node =  MDNode::get(BB.getContext(), ConstantAsMetadata::get(ConstantInt::get(Type::getInt64Ty(BB.getContext()), raw_id)));
            term->setMetadata(M.getMDKindID("basicblock.id"), node);
            inst_blocks++;
          }
          else {
            uint64_t child_id =read_id_from_metadata(term->getMetadata(M.getMDKindID("basicblock.id")));
            childs_map[parent_id].insert(child_id);
          }
        }
      }
    }

  OKF("Generated Unique BasicBlock ID for %u locations.", inst_blocks);
#ifdef DEBUG
  for (auto& [parent, set]: childs_map) {
    errs() << "parent: " << parent << "\n" << "children: ";
    for (auto& child : set) {
      errs() <<child << " ";
    }
    errs() << "\n";
  }
#endif

#if LLVM_VERSION_MAJOR <= 11
  return true;
#else
  return PreservedAnalyses();
#endif
}

#if LLVM_VERSION_MAJOR <= 11
static void registerUniqueIDPass(const PassManagerBuilder &,
                                 legacy::PassManagerBase &PM) {

  PM.add(new UniqueID());
}

static RegisterStandardPasses
    RegisterUniqueIDPass(PassManagerBuilder::EP_ModuleOptimizerEarly,
                         registerUniqueIDPass);

static RegisterStandardPasses
    RegisterUniqueIDPass0(PassManagerBuilder::EP_EnabledOnOptLevel0,
                          registerUniqueIDPass);

#endif
