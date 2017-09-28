// note: you can use the tool at https://qfox.github.io/logic-table-filter/ to test some of these tricks
// enter the names of the vars, the formulae (in proper JS), and the var considered a leaf and you can
// quickly see whether the rewrite is valid or not.

import {
  ASSERT,
  getTerm,
  TRACE,
  TRACE_MORPH,
  THROW,
} from '../../fdlib/src/helpers';
import {
  EMPTY,

  domain__debug,
  domain_arrToSmallest,
  domain_containsValue,
  domain_createEmpty,
  domain_createRange,
  domain_createValue,
  domain_getValue,
  domain_hasNoZero,
  domain_hasZero,
  domain_intersection,
  domain_intersectionValue,
  domain_isBool,
  domain_isBooly,
  domain_isBoolyPair,
  domain_isSolved,
  domain_isZero,
  domain_max,
  domain_min,
  domain_plus,
  domain_removeGte,
  domain_removeGtUnsafe,
  domain_removeLte,
  domain_removeLtUnsafe,
  domain_removeValue,
  domain_resolveAsBooly,
  domain_size,
} from '../../fdlib/src/domain';

import {
  ML_ALL,
  ML_NOBOOL,
  ML_NOLEAF,
  ML_DIFF,
  ML_DIV,
  ML_IMP,
  ML_ISALL,
  ML_ISDIFF,
  ML_ISLT,
  ML_ISLTE,
  ML_ISNALL,
  ML_ISNONE,
  ML_ISSAME,
  ML_ISSOME,
  ML_JMP,
  ML_JMP32,
  ML_LT,
  ML_LTE,
  ML_MINUS,
  ML_NALL,
  ML_NIMP,
  ML_NONE,
  ML_NOOP,
  ML_NOOP2,
  ML_NOOP3,
  ML_NOOP4,
  ML_PRODUCT,
  ML_SAME,
  ML_SOME,
  ML_START,
  ML_STOP,
  ML_SUM,
  ML_XNOR,
  ML_XOR,

  SIZEOF_V,
  SIZEOF_W,
  SIZEOF_VVV,
  SIZEOF_C,
  SIZEOF_C_2,
  SIZEOF_CR_2,

  OFFSET_C_A,
  OFFSET_C_B,
  OFFSET_C_C,
  OFFSET_C_R,

  ml__debug,
  ml__opName,
  ml_compileJumpAndConsolidate,
  ml_compileJumpSafe,
  ml_dec8,
  ml_dec16,
  ml_dec32,
  ml_enc8,
  ml_enc16,
  ml_eliminate,
  ml_getOpSizeSlow,
  ml_getRecycleOffsets,
  ml_heapSort16bitInline,
  ml_recycles,
  ml_throw,
  ml_validateSkeleton,

  ml_any2c,
  ml_cx2cx,
  ml_c2c2,
  ml_cr2c,
  ml_cr2c2,
  ml_cr2cr2,
} from './ml';
import {
  BOUNTY_FLAG_NOT_BOOLY,
  //BOUNTY_FLAG_OTHER,
  BOUNTY_MAX_OFFSETS_TO_TRACK,
  //BOUNTY_NO_FLAGS,

  BOUNTY_FLAG_IMP_LHS,
  BOUNTY_FLAG_IMP_RHS,
  BOUNTY_FLAG_ISALL_ARG,
  BOUNTY_FLAG_ISALL_RESULT,
  BOUNTY_FLAG_ISSOME_RESULT,
  BOUNTY_FLAG_ISSAME_ARG,
  BOUNTY_FLAG_ISSAME_RESULT,
  BOUNTY_FLAG_ISLTE_ARG,
  BOUNTY_FLAG_LTE_LHS,
  BOUNTY_FLAG_LTE_RHS,
  BOUNTY_FLAG_NALL,
  BOUNTY_FLAG_DIFF,
  BOUNTY_FLAG_SOME,
  BOUNTY_FLAG_SUM_RESULT,
  BOUNTY_FLAG_XOR,

  bounty__debug,
  bounty__debugMeta,
  bounty_collect,
  bounty_getCounts,
  bounty_getMeta,
  bounty_getOffset,
  bounty_markVar,
} from './bounty';
import {
  m2d__debug,
} from './ml2dsl';

// BODY_START

const ML_BOOLY_NO = 0;
const ML_BOOLY_YES = 1;
const ML_BOOLY_MAYBE = 2;

function cutter(ml, problem, once) {
  TRACE('\n ## cutter', ml.length < 50 ? ml.join(' ') : '');

  let term = getTerm();

  let getDomain = problem.getDomain;
  let setDomain = problem.setDomain;
  let addAlias = problem.addAlias;
  let getAlias = problem.getAlias;
  let solveStack = problem.solveStack;
  let leafs = problem.leafs;
  let isConstant = problem.isConstant;

  let pc = 0;

  let bounty;

  let stacksBefore;
  let emptyDomain = false;
  let changes = 0;
  let loops = 0;
  let requestAnotherCycle = false; // when true this will force another cycle so the minimizer runs again
  do {
    term.time('-> cut_loop ' + loops);
    TRACE(' # start cutter outer loop', loops);
    bounty = bounty_collect(ml, problem, bounty);

    TRACE('\n#### Problem state between bounty and cutter: ###');
    TRACE(ml__debug(ml, 0, 20, problem));
    TRACE(m2d__debug(problem));

    stacksBefore = solveStack.length;
    changes = 0;
    cutLoop();
    term.timeEnd('-> cut_loop ' + loops);
    term.log('   - end cutter outer loop', loops, ', removed:', solveStack.length - stacksBefore, ' vars, total changes:', changes, ', emptyDomain =', emptyDomain, 'once=', once);

    ++loops;
  } while (!emptyDomain && changes && !once && !requestAnotherCycle);

  TRACE('## exit cutter', emptyDomain ? '[there was an empty domain]' : requestAnotherCycle ? '[explicitly requesting another cycle]' : loops > 1 ? '[it might not be done]' : '[it is done]');
  if (emptyDomain) return -1;
  return loops + (requestAnotherCycle ? 1 : 0);

  function somethingChanged() {
    ++changes;
  }

  function readIndex(ml, offset) {
    ASSERT(ml instanceof Uint8Array, 'ml should be a buffer');
    ASSERT(typeof offset === 'number' && offset >= 0 && offset <= ml.length, 'expecting valid offset');
    ASSERT(arguments.length === 2, 'only two args');
    return getAlias(ml_dec16(ml, offset));
  }

  function getMeta(bounty, index, keepBoolyFlags, _debug) {
    ASSERT(typeof index === 'number' && index >= 0 && index <= 0xffff, 'expecting valid index');
    ASSERT(arguments.length === 2 || arguments.length === 3, 'only two or three args');
    if (!isConstant(index)) {
      let meta = bounty_getMeta(bounty, index, _debug);
      if (!keepBoolyFlags) return scrubBoolyFlag(meta);
      return meta;
    }
    return 0;
  }

  function scrubBoolyFlag(meta) {
    return (meta | BOUNTY_FLAG_NOT_BOOLY) ^ BOUNTY_FLAG_NOT_BOOLY;
  }

  function hasFlags(meta, flags) {
    return (meta & flags) === flags;
  }

  function getCounts(bounty, index) {
    ASSERT(typeof index === 'number' && index >= 0 && index <= 0xffff, 'expecting valid index');
    ASSERT(arguments.length === 2, 'no more than two args');
    if (!isConstant(index)) return bounty_getCounts(bounty, index);
    return 0;
  }

  // ##############

  function cutLoop() {
    TRACE('\n#### - inner cutLoop');
    pc = 0;
    while (pc < ml.length && !emptyDomain && !requestAnotherCycle) {
      let pcStart = pc;
      let op = ml[pc];
      TRACE(' -- CU pc=' + pc, ', op=', op, ml__opName(op));
      TRACE(' -> op: ' + ml__debug(ml, pc, 1, problem, true));
      ASSERT(ml_validateSkeleton(ml, 'cutLoop'));
      switch (op) {
        case ML_ALL:
          return ml_throw(ml, pc, 'all() should be solved and eliminated');
        case ML_DIFF:
          cut_diff(ml, pc);
          break;
        case ML_DIV:
          pc += SIZEOF_VVV;
          break;
        case ML_IMP:
          cut_imp(ml, pc);
          break;
        case ML_ISALL:
          cut_isall(ml, pc);
          break;
        case ML_ISDIFF:
          cut_isdiff(ml, pc);
          break;
        case ML_ISLT:
          cut_islt(ml, pc);
          break;
        case ML_ISLTE:
          cut_islte(ml, pc);
          break;
        case ML_ISNALL:
          cut_isnall(ml, pc);
          break;
        case ML_ISSAME:
          cut_issame(ml, pc);
          break;
        case ML_ISSOME:
          cut_issome(ml, pc);
          break;
        case ML_ISNONE:
          TRACE('(skipped) issome/isnone', pc);
          let nlen = ml_dec16(ml, pc + 1);
          pc += SIZEOF_C + nlen * 2 + 2;
          break;
        case ML_LT:
          cut_lt(ml, pc);
          break;
        case ML_LTE:
          cut_lte(ml, pc);
          break;
        case ML_MINUS:
          pc += SIZEOF_VVV;
          break;
        case ML_NALL:
          cut_nall(ml, pc);
          break;
        case ML_NIMP:
          TRACE('(skipped) nimp', pc);
          pc += SIZEOF_C_2;
          break;
        case ML_NONE:
          return ml_throw(ml, pc, 'nors should be solved and eliminated');
        case ML_PRODUCT:
          TRACE('(skipped) product', pc);
          let plen = ml_dec16(ml, pc + 1);
          pc += SIZEOF_C + plen * 2 + 2;
          break;
        case ML_SAME:
          return ml_throw(ml, pc, 'eqs should be aliased and eliminated');
        case ML_SOME:
          cut_some(ml, pc);
          break;
        case ML_SUM:
          cut_sum(ml, pc);
          break;
        case ML_XOR:
          cut_xor(ml, pc);
          break;
        case ML_XNOR:
          cut_xnor(ml, pc);
          break;


        case ML_START:
          if (pc !== 0) return ml_throw(ml, pc, ' ! compiler problem @', pcStart);
          ++pc;
          break;
        case ML_STOP:
          return;

        case ML_NOBOOL:
        case ML_NOLEAF:
          pc += SIZEOF_V;
          break;

        case ML_JMP:
          cut_moveTo(ml, pc, SIZEOF_V + ml_dec16(ml, pc + 1));
          break;
        case ML_JMP32:
          cut_moveTo(ml, pc, SIZEOF_W + ml_dec32(ml, pc + 1));
          break;

        case ML_NOOP:
          cut_moveTo(ml, pc, 1);
          break;
        case ML_NOOP2:
          cut_moveTo(ml, pc, 2);
          break;
        case ML_NOOP3:
          cut_moveTo(ml, pc, 3);
          break;
        case ML_NOOP4:
          cut_moveTo(ml, pc, 4);
          break;

        default:
          getTerm().error('(cut) unknown op', pc, ' at', pc);
          ml_throw(ml, pc, '(cut) unknown op', pc);
      }
    }
    if (emptyDomain) {
      TRACE('Ended up with an empty domain');
      return;
    }
    if (requestAnotherCycle) {
      TRACE('Stopped cutloop prematurely because another minimizer cycle was requested');
      return;
    }
    TRACE('the implicit end; ml desynced');
    THROW('ML OOB');
  }

  function cut_diff(ml, offset) {
    let argCount = ml_dec16(ml, offset + 1);

    TRACE(' ! cut_diff;', argCount, 'args');

    let indexA = readIndex(ml, offset + OFFSET_C_A);
    let countsA = getCounts(bounty, indexA);
    if (countsA > 1 && countsA < BOUNTY_MAX_OFFSETS_TO_TRACK) {
      // search all counts for a second SOME
      if (desubset_diff(ml, offset, argCount, indexA, countsA)) return;
    }

    if (argCount !== 2) {
      TRACE(' - did not have 2 args, bailing for now');
      pc += SIZEOF_C + argCount * 2;
      return;
    }

    // for the remainder, these are NEQ cuts (diff[2])

    let indexB = readIndex(ml, offset + OFFSET_C_B);
    let countsB = getCounts(bounty, indexB);

    TRACE(' - diff:', indexA, '!=', indexB, '::', domain__debug(getDomain(indexA, true)), '!=', domain__debug(getDomain(indexB, true)));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    TRACE('  - counts:', countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexA), bounty__debugMeta(bounty, indexB));

    if (indexA === indexB) {
      TRACE(' - index A == B, redirecting to minimizer');
      requestAnotherCycle = true;
      return;
    }

    if (countsA === 1) {
      return leaf_diff_pair(ml, offset, indexA, indexB, indexA, indexB);
    }

    if (countsB === 1) {
      return leaf_diff_pair(ml, offset, indexB, indexA, indexA, indexB);
    }

    let TRICK_INV_DIFF_FLAGS = BOUNTY_FLAG_LTE_LHS | BOUNTY_FLAG_LTE_RHS | BOUNTY_FLAG_SOME | BOUNTY_FLAG_NALL | BOUNTY_FLAG_IMP_LHS | BOUNTY_FLAG_IMP_RHS;

    if (countsA > 1 && countsA <= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      let metaA = getMeta(bounty, indexA);

      // check if it has any targeted ops, then check if it has no other stuff
      let hasGoodOps = (metaA & TRICK_INV_DIFF_FLAGS) > 0;
      let hasBadOps = (metaA | TRICK_INV_DIFF_FLAGS | BOUNTY_FLAG_DIFF) ^ (TRICK_INV_DIFF_FLAGS | BOUNTY_FLAG_DIFF);
      TRACE('  - has good:', hasGoodOps, ', hasBad:', hasBadOps);
      // TODO: why are we checking diff here? shouldnt that have been done above? and why not checking that below?
      if (hasFlags(metaA, BOUNTY_FLAG_DIFF) && hasGoodOps && !hasBadOps) {
        if (trick_diff_elimination(offset, indexA, countsA, indexB)) return;
      }

      if (hasFlags(metaA, BOUNTY_FLAG_DIFF | BOUNTY_FLAG_XOR)) {
        if (trick_diff_xor(ml, offset, indexA, countsA, indexB)) return;
      }

      if (trick_diff_alias(indexA, indexB, countsA)) return;
    }

    if (countsB > 1 && countsB <= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      let metaB = getMeta(bounty, indexB);

      // first remove the booly flag, then check if it has any targeted ops, then check if it has no other stuff
      let hasGoodOps = (metaB & TRICK_INV_DIFF_FLAGS) > 0;
      let hasBadOps = (metaB | TRICK_INV_DIFF_FLAGS | BOUNTY_FLAG_DIFF) ^ (TRICK_INV_DIFF_FLAGS | BOUNTY_FLAG_DIFF);
      TRACE('  - has good:', hasGoodOps, ', hasBad:', hasBadOps);
      if (hasGoodOps && !hasBadOps) {
        if (trick_diff_elimination(offset, indexB, countsB, indexA)) return;
      }

      if (hasFlags(metaB, BOUNTY_FLAG_DIFF | BOUNTY_FLAG_XOR)) {
        if (trick_diff_xor(ml, offset, indexB, countsB, indexA)) return;
      }

      if (trick_diff_alias(indexB, indexA, countsB)) return;

      let A = getDomain(indexA, true);
      let B = getDomain(indexB, true);
      if (domain_isBoolyPair(A) && A === B) {
        TRACE(' - A and B are booly pair and equal so turn this DIFF into a XOR');
        TRACE_MORPH('A:[00xx] != B:[00xx]', 'A ^ B');
        ml_enc8(ml, offset, ML_XOR);
        bounty_markVar(bounty, indexA);
        bounty_markVar(bounty, indexB);
        somethingChanged();
        return;
      }
    }

    TRACE(' - cut_diff changed nothing');
    pc += SIZEOF_C_2;
  }

  function cut_imp(ml, offset) {
    let indexA = readIndex(ml, offset + OFFSET_C_A);
    let indexB = readIndex(ml, offset + OFFSET_C_B);

    let A = getDomain(indexA, true);
    let B = getDomain(indexB, true);

    let countsA = getCounts(bounty, indexA);
    let countsB = getCounts(bounty, indexB);

    TRACE(' ! cut_imp;', indexA, '->', indexB, ', ', domain__debug(A), '->', domain__debug(B));
    TRACE('  - counts:', countsA, '->', countsB, ', meta:', bounty__debugMeta(bounty, indexA), '->', bounty__debugMeta(bounty, indexB));

    if (indexA === indexB) {
      TRACE(' - index A == B, redirecting to minimizer');
      requestAnotherCycle = true;
      return;
    }

    if (!domain_isBooly(A) || domain_hasNoZero(B)) {
      TRACE(' - this imp is already solved, bouncing back to minimizer');
      requestAnotherCycle = true;
      return false;
    }

    if (countsA === 1) {
      return leaf_imp(ml, offset, indexA, indexB, true);
    }

    if (countsB === 1) {
      return leaf_imp(ml, offset, indexA, indexB, false);
    }

    if (countsA > 0) {
      let metaA = getMeta(bounty, indexA);
      ASSERT(metaA & BOUNTY_FLAG_IMP_LHS, 'should be');

      if (metaA === BOUNTY_FLAG_IMP_LHS) {
        if (trick_only_implhs_leaf(ml, indexA, countsA)) return;
      }

      if (metaA === BOUNTY_FLAG_NALL || metaA === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_IMP_LHS)) {
        if (trick_implhs_nall_leaf(ml, indexA, countsA)) return;
      }

      if (countsA === 2) {
        if (metaA === (BOUNTY_FLAG_IMP_LHS | BOUNTY_FLAG_SOME)) {
          if (trick_implhs_some_leaf(ml, offset, indexA, countsA)) return;
        }
      }

      if (hasFlags(metaA, BOUNTY_FLAG_ISALL_RESULT)) {
        // this trick has isall subsume the lte, so no need for R to be leaf
        if (trick_implhs_isall_2shared(ml, offset, indexA, countsA)) return;

        // this trick requires R to be leaf
        if (countsA === 2) {
          if (trick_isall_implhs_1shared(ml, offset, indexA, countsA)) return;
        }
      }

      if (countsA >= 3) {
        if (metaA === (BOUNTY_FLAG_SOME | BOUNTY_FLAG_NALL | BOUNTY_FLAG_IMP_LHS)) {
          if (trick_implhs_nalls_some(indexA, countsA)) return;
        }
        if (metaA === (BOUNTY_FLAG_SOME | BOUNTY_FLAG_NALL | BOUNTY_FLAG_IMP_LHS | BOUNTY_FLAG_IMP_RHS)) {
          if (trick_impboth_nall_some(indexA, countsA)) return;
        }
      }
    }

    if (domain_isBool(A) && domain_isBool(B)) {
      if (countsB === 2) {
        let metaB = getMeta(bounty, indexB, true); // keep booly flags

        if (metaB === (BOUNTY_FLAG_IMP_RHS | BOUNTY_FLAG_ISALL_RESULT)) {
          if (trick_imprhs_isall_entry(indexB, offset, countsB, indexA)) return;
        }
      }
    }

    TRACE(' - cut_imp did nothing');
    pc += SIZEOF_C_2;
  }

  function cut_isall(ml, offset) {
    let argCount = ml_dec16(ml, offset + 1);
    let argsOffset = offset + SIZEOF_C;
    let opSize = SIZEOF_C + argCount * 2 + 2;

    let indexR = readIndex(ml, argsOffset + argCount * 2);
    let countsR = getCounts(bounty, indexR);
    TRACE(' ! cut_isall; R=', indexR, ', counts:', countsR, ', metaR:', bounty__debugMeta(bounty, indexR));
    ASSERT(!countsR || !domain_isSolved(getDomain(indexR, true)), 'if it has counts it shouldnt be solved', countsR, indexR, domain__debug(getDomain(indexR, true)));

    if (countsR > 0 && countsR < BOUNTY_MAX_OFFSETS_TO_TRACK) {
      if (countsR === 1) {
        // when R is a leaf, the isall args are not bound by it nor the reifier so they are free
        return leaf_isall(ml, offset, argCount, indexR);
      }

      let metaR = getMeta(bounty, indexR);

      if (metaR === (BOUNTY_FLAG_ISALL_RESULT | BOUNTY_FLAG_ISALL_ARG)) {
        if (leaf_isall_arg_result(ml, indexR, countsR)) return;
      }

      if (countsR === 2) {
        if (metaR === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_ISALL_RESULT)) {
          if (trick_isall_nall_2shared(ml, indexR, offset, countsR)) return;
        }
      }

      if (metaR === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_ISALL_RESULT)) {
        if (trick_isall_nall_1shared(ml, indexR, offset, countsR)) return;
      }
    }

    TRACE('   cut_isall changed nothing');
    pc += opSize;
  }

  function cut_isdiff(ml, offset) {
    let argCount = ml_dec16(ml, offset + 1);
    let indexR = readIndex(ml, offset + SIZEOF_C + argCount * 2);

    TRACE(' ! cut_isdiff; ', indexR, '::', domain__debug(getDomain(indexR, true)), ', args:', argCount);

    if (argCount !== 2) {
      TRACE(' - argCount=', argCount, ', bailing because it is not 2');
      pc = offset + SIZEOF_C + argCount * 2 + 2;
      return;
    }

    let indexA = readIndex(ml, offset + OFFSET_C_A);
    let indexB = readIndex(ml, offset + OFFSET_C_B);

    let countsA = getCounts(bounty, indexA);
    let countsB = getCounts(bounty, indexB);
    let countsR = getCounts(bounty, indexR);

    TRACE(' -', indexR, '=', indexA, '!=?', indexB, '::', domain__debug(getDomain(indexR, true)), '=', domain__debug(getDomain(indexA, true)), '!=?', domain__debug(getDomain(indexB, true)));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    ASSERT(!countsR || !domain_isSolved(getDomain(indexR, true)), 'if it has counts it shouldnt be solved', countsR, indexR, domain__debug(getDomain(indexR, true)));
    TRACE('  - counts:', countsR, countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexR), '=', bounty__debugMeta(bounty, indexA), '!=?', bounty__debugMeta(bounty, indexB));

    if (countsR === 1) {
      return leaf_isdiff(ml, offset, indexA, indexB, indexR, indexR);
    }

    if (countsA === 1) {
      ASSERT(!domain_isSolved(getDomain(indexA, true)), 'A cannot be solved (bounty ignores constants so count would be 0)');
      if (canCutIsdiffForArg(indexA, indexB, indexR)) {
        return leaf_isdiff(ml, offset, indexA, indexB, indexR, indexA);
      }
    }

    if (countsB === 1) {
      // not covered, kept here just in case the above assertion doesnt hold in prod
      ASSERT(!domain_isSolved(getDomain(indexB, true)), 'B cannot be solved (bounty ignores constants so count would be 0)');
      if (canCutIsdiffForArg(indexB, indexA, indexR)) {
        return leaf_isdiff(ml, offset, indexA, indexB, indexR, indexB);
      }
    }

    let R = getDomain(indexR, true);
    let A = getDomain(indexA, true);
    let B = getDomain(indexB, true);

    if (domain_isBoolyPair(R)) {
      if (domain_isBoolyPair(A) && domain_isSolved(B)) {
        // R:[00yy] = A:[00xx] !=? 0/x
        if (domain_isZero(B)) {
          TRACE_MORPH('R = A !=? 0', '!(R ^ A)');
          ml_cr2c2(ml, offset, 2, ML_XNOR, indexA, indexR);
          bounty_markVar(bounty, indexA);
          bounty_markVar(bounty, indexB);
          bounty_markVar(bounty, indexR);
          somethingChanged();
          return;
        } else if (domain_max(A) === domain_getValue(B)) {
          // must confirm A contains B because it may in some edge cases not
          TRACE_MORPH('R = A:[00xx] !=? x', 'R ^ A');
          ml_cr2c2(ml, offset, 2, ML_XOR, indexA, indexR);
          bounty_markVar(bounty, indexA);
          bounty_markVar(bounty, indexB);
          bounty_markVar(bounty, indexR);
          somethingChanged();
          return;
        }
      }
      if (domain_isSolved(A) && domain_isBoolyPair(B)) {
        // R:[00yy] = 0/x !=? A:[00xx]
        if (domain_isZero(A)) {
          TRACE_MORPH('R = 0 !=? B', '!(R ^ B)');
          ml_cr2c2(ml, offset, 2, ML_XNOR, indexB, indexR);
          bounty_markVar(bounty, indexA);
          bounty_markVar(bounty, indexB);
          bounty_markVar(bounty, indexR);
          somethingChanged();
          return;
        } else if (domain_max(B) === domain_getValue(A)) {
          // must confirm B contains A because it may in some edge cases not
          TRACE_MORPH('R = x !=? B:[00xx]', 'R ^ B');
          ml_cr2c2(ml, offset, 2, ML_XOR, indexB, indexR);
          bounty_markVar(bounty, indexA);
          bounty_markVar(bounty, indexB);
          bounty_markVar(bounty, indexR);
          somethingChanged();
          return;
        }
      }
    }

    TRACE(' - cut_isdiff changed nothing');
    pc = offset + SIZEOF_CR_2;
  }
  function canCutIsdiffForArg(indexL, indexO, indexR) {
    TRACE('   - canCutIsdiffForArg;', indexL, indexO, indexR, '->', domain__debug(getDomain(indexR, true)), '=', domain__debug(getDomain(indexL, true)), '!=?', domain__debug(getDomain(indexO, true)));
    // an isdiff with 2 args can only be leaf-cut on an arg if the leaf can represent all outcomes
    // so if C is solved, solve as SAME or DIFF.
    // otherwise make sure the leaf contains all vars of the other var and at least one var that's not in there
    // as long as that's impossible we can't cut it without implicitly forcing vars

    // first check whether R is booly-solved, this would mean fewer values to check

    let R = getDomain(indexR, true);
    if (domain_hasNoZero(R)) {
      TRACE('    - R=0 and size(L)>2 so cuttable');
      // L contains at least two values so regardless of the state of O, L can fulfill !=
      ASSERT(domain_size(L) >= 2, 'see?');
      return true;
    }

    // R=1 or R=booly is more involved because we at least
    // need to know whether L contains all values in O

    let L = getDomain(indexL, true);
    let O = getDomain(indexO, true);
    let LO = domain_intersection(L, O); // <-- this tells us that
    TRACE('    - LO:', domain__debug(LO));
    if (domain_isZero(R)) {
      // only cut if we are certain L can represent eq in any way O solves

      if (!LO) {
        TRACE('    - R>=1 and A contains no value in B so reject');
        // no values in L and O match so reject
        setDomain(indexL, domain_createEmpty(), false, true);
        return false;
      }

      if (LO === O) {
        TRACE('    - R>=1 and A contains all values in B so cuttable');
        // this means L contains all values in O (and maybe more, dont care)
        // which means L can uphold the eq for any value of O
        return true;
      }

      TRACE('    - R>=1 and A contains some but not all B so not cuttable, yet');
      // there's no guarantee O solves to a value in L so we cant cut safely
      return true;
    }

    TRACE('    - R unresolved, cuttable if L contains all values in O and then some;', LO === O, LO !== L, 'so:', LO === O && LO !== L);
    // we dont know R so L should contain all values in O (LO==O) and at least
    // one value not in O (LO != O), to consider this a safe cut. otherwise dont.
    return LO === O && LO !== L;
  }

  function cut_islt(ml, offset) {
    let indexA = readIndex(ml, offset + 1);
    let indexB = readIndex(ml, offset + 3);
    let indexR = readIndex(ml, offset + 5);

    let countsA = getCounts(bounty, indexA);
    let countsB = getCounts(bounty, indexB);
    let countsR = getCounts(bounty, indexR);

    TRACE(' ! cut_islt; ', indexR, '=', indexA, '<?', indexB, '::', domain__debug(getDomain(indexR, true)), '=', domain__debug(getDomain(indexA, true)), '<?', domain__debug(getDomain(indexB, true)));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    ASSERT(!countsR || !domain_isSolved(getDomain(indexR, true)), 'if it has counts it shouldnt be solved', countsR, indexR, domain__debug(getDomain(indexR, true)));
    TRACE('  - counts:', countsR, countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexR), '=', bounty__debugMeta(bounty, indexA), '<?', bounty__debugMeta(bounty, indexB));

    if (countsR === 1) {
      return leaf_islt(ml, offset, indexA, indexB, indexR, indexR);
    }

    if (countsA === 1) {
      if (canCutIsltForArg(indexA, indexB, indexR, indexA, indexB)) {
        return leaf_islt(ml, offset, indexA, indexB, indexR, indexA);
      }
    }

    if (countsB === 1) {
      if (canCutIsltForArg(indexB, indexA, indexR, indexA, indexB)) {
        return leaf_islt(ml, offset, indexA, indexB, indexR, indexB);
      }
    }

    TRACE(' - cut_islt changed nothing');
    pc = offset + SIZEOF_VVV;
  }
  function canCutIsltForArg(indexL, indexO, indexR, indexA, indexB) {
    TRACE('   - canCutIsltForArg;', indexL, indexO, indexR, '->', domain__debug(getDomain(indexR, true)), '=', domain__debug(getDomain(indexA, true)), '<?', domain__debug(getDomain(indexB, true)));
    // an islt can only be leaf-cut on an arg if the leaf can represent all outcomes
    // so if C is solved, solve as SAME or DIFF.
    // otherwise make sure the leaf contains all vars of the other var and at least one var that's not in there
    // as long as that's impossible we can't cut it without implicitly forcing vars

    // keep in mind A and B are ordered and cant be swapped

    // first check whether R is booly-solved, this would mean fewer values to check

    let A = getDomain(indexA, true);
    let B = getDomain(indexB, true);
    let R = getDomain(indexR, true);

    if (domain_hasNoZero(R)) {
      TRACE('   - R>0');
      // if L is A, O must have at least one value below min(B). otherwise it must have at least one value > max(A).
      if (indexL === indexA) return domain_min(A) < domain_min(B);
      else return domain_max(B) > domain_max(A);
    }

    if (domain_isZero(R)) {
      TRACE('   - R=0');
      // if L is A, O must have at least one value >= min(B). otherwise it must have at least one value <= max(A).
      if (indexL === indexA) return domain_min(A) >= domain_min(B);
      else return domain_max(B) <= domain_max(A);
    }

    // R unresolved. O must have at least both values to represent R=0 and R>=1

    if (indexL === indexA) {
      TRACE('   - R unresolved, L=A', domain_min(A) < domain_min(B), domain_max(A) >= domain_max(B));
      // L must contain a value < min(B) and a value >= max(B)
      return domain_min(A) < domain_min(B) && domain_max(A) >= domain_max(B);
    }

    TRACE('   - R unresolved, L=B', domain_max(B), '>', domain_max(A), '->', domain_max(B) > domain_max(A), domain_min(B), '<=', domain_min(A), '->', domain_min(B) <= domain_min(A));
    // L is B, L must contain one value above max(A) and one value <= min(A)
    return domain_max(B) > domain_max(A) && domain_min(B) <= domain_min(A);
  }

  function cut_islte(ml, offset) {
    let indexA = readIndex(ml, offset + 1);
    let indexB = readIndex(ml, offset + 3);
    let indexR = readIndex(ml, offset + 5);

    let countsA = getCounts(bounty, indexA);
    let countsB = getCounts(bounty, indexB);
    let countsR = getCounts(bounty, indexR);

    TRACE(' ! cut_islte; ', indexR, '=', indexA, '<=?', indexB, '::', domain__debug(getDomain(indexR, true)), '=', domain__debug(getDomain(indexA, true)), '<=?', domain__debug(getDomain(indexB, true)));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    ASSERT(!countsR || !domain_isSolved(getDomain(indexR, true)), 'if it has counts it shouldnt be solved', countsR, indexR, domain__debug(getDomain(indexR, true)));
    TRACE('  - counts:', countsR, countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexR), '=', bounty__debugMeta(bounty, indexA), '<=?', bounty__debugMeta(bounty, indexB));

    let R = getDomain(indexR, true);
    if (!domain_isBooly(R)) {
      TRACE(' - R is already booly solved, requesting another minifier sweep, bailing');
      requestAnotherCycle = true;
      return;
    }

    if (countsR === 1) {
      return leaf_islte(ml, offset, indexA, indexB, indexR, indexR);
    }

    let A = getDomain(indexA, true);
    let B = getDomain(indexB, true);

    if (countsA === 1) {
      if (canCutIslteForArg(indexA, indexB, indexA, indexB, A, B)) {
        return leaf_islte(ml, offset, indexA, indexB, indexR, indexA);
      }
    }

    if (countsB === 1) {
      if (canCutIslteForArg(indexB, indexA, indexA, indexB, A, B)) {
        return leaf_islte(ml, offset, indexA, indexB, indexR, indexB);
      }
    }

    if (countsR > 0 && countsR < BOUNTY_MAX_OFFSETS_TO_TRACK) {
      if (domain_isSolved(A)) {
        // R = x <=? B
        let metaR = getMeta(bounty, indexR);
        if (hasFlags(metaR, BOUNTY_FLAG_IMP_RHS)) {
          let metaB = getMeta(bounty, indexB);
          if (hasFlags(metaB, BOUNTY_FLAG_IMP_LHS)) {
            if (trick_imp_islte_c_v(offset, indexR, indexA, indexB, countsR)) return;
          }
        }
      }
      if (domain_isSolved(B)) {
        // R = A <=? x
        let metaR = getMeta(bounty, indexR);
        if (hasFlags(metaR, BOUNTY_FLAG_IMP_RHS)) {
          let metaA = getMeta(bounty, indexA);
          if (hasFlags(metaA, BOUNTY_FLAG_IMP_LHS)) {
            if (trick_imp_islte_v_c(offset, indexR, indexA, indexB, countsR)) return;
          }
        }
      }
    }

    TRACE(' - cut_islte changed nothing');
    pc = offset + SIZEOF_VVV;
  }
  function canCutIslteForArg(indexL, indexO, indexA, indexB, A, B) {
    TRACE('   - canCutIslteForArg;', indexL, indexO, domain__debug(getDomain(indexA, true)), '<=?', domain__debug(getDomain(indexB, true)));
    // an islte can only be leaf-cut on an arg if the leaf can represent all outcomes
    // so if C is solved, solve as SAME or DIFF.
    // otherwise make sure the leaf contains all vars of the other var and at least one var that's not in there
    // as long as that's impossible we can't cut it without implicitly forcing vars

    // keep in mind A and B are ordered and cant be swapped

    // R unresolved. O must have at least both values to represent R=0 and R>=1

    if (indexL === indexA) {
      TRACE('   - L=A', domain_min(A) <= domain_min(B), domain_max(A) > domain_max(B));
      // L must contain a value <= min(B) and a value > max(B)
      return domain_min(A) <= domain_min(B) && domain_max(A) > domain_max(B);
    }

    TRACE('   - L=B', domain_max(B), '>=', domain_max(A), '->', domain_max(B) >= domain_max(A), domain_min(B), '<', domain_min(A), '->', domain_min(B) < domain_min(A));
    // L is B, L must contain one value gte max(A) and one value below min(A)
    return domain_max(B) >= domain_max(A) && domain_min(B) < domain_min(A);
  }

  function cut_isnall(ml, offset) {
    let argCount = ml_dec16(ml, offset + 1);
    let argsOffset = offset + SIZEOF_C;
    let opSize = SIZEOF_C + argCount * 2 + 2;

    let indexR = readIndex(ml, argsOffset + argCount * 2);
    let countsR = getCounts(bounty, indexR);

    TRACE(' ! cut_isnall; R=', indexR);
    ASSERT(!countsR || !domain_isSolved(getDomain(indexR, true)), 'if it has counts it shouldnt be solved', countsR, indexR, domain__debug(getDomain(indexR, true)));

    if (countsR === 1) {
      return leaf_isnall(ml, offset, argCount, indexR, countsR);
    }

    pc += opSize;
  }

  function cut_issame(ml, offset) {
    let argCount = ml_dec16(ml, offset + 1);

    TRACE(' ! cut_issame');

    if (argCount !== 2) {
      TRACE(' - argCount != 2 so bailing, for now');
      pc = offset + SIZEOF_C + argCount * 2 + 2;
      return;
    }

    let indexA = readIndex(ml, offset + OFFSET_C_A);
    let indexB = readIndex(ml, offset + OFFSET_C_B);
    let indexR = readIndex(ml, offset + OFFSET_C_C);

    let countsA = getCounts(bounty, indexA);
    let countsB = getCounts(bounty, indexB);
    let countsR = getCounts(bounty, indexR);

    TRACE(' - cut_issame; ', indexR, '=', indexA, '==?', indexB, '::', domain__debug(getDomain(indexR, true)), '=', domain__debug(getDomain(indexA, true)), '==?', domain__debug(getDomain(indexB, true)));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    ASSERT(!countsR || !domain_isSolved(getDomain(indexR, true)), 'if it has counts it shouldnt be solved', countsR, indexR, domain__debug(getDomain(indexR, true)));
    TRACE('  - counts:', countsR, countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexR), '=', bounty__debugMeta(bounty, indexA), '==?', bounty__debugMeta(bounty, indexB));

    if (countsR === 1) {
      return leaf_issame(ml, offset, indexA, indexB, indexR, indexR);
    }

    if (countsA === 1) {
      ASSERT(!domain_isSolved(getDomain(indexA, true)), 'A cannot be solved (bounty ignores constants so count would be 0)');
      if (canCutIssameForArg(indexA, indexB, indexR)) {
        return leaf_issame(ml, offset, indexA, indexB, indexR, indexA);
      }
    }

    if (countsB === 1) {
      // not covered, kept here just in case the above assertion doesnt hold in prod
      ASSERT(!domain_isSolved(getDomain(indexB, true)), 'B cannot be solved (bounty ignores constants so count would be 0)');
      if (canCutIssameForArg(indexB, indexA, indexR)) {
        return leaf_issame(ml, offset, indexA, indexB, indexR, indexB);
      }
    }

    TRACE(' - no change from cut_issame');
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'should have 2 args');
    pc = offset + SIZEOF_CR_2;
  }
  function canCutIssameForArg(indexL, indexO, indexR) {
    TRACE('   - canCutIssameForArg;', indexL, indexO, indexR, '->', domain__debug(getDomain(indexR, true)), '=', domain__debug(getDomain(indexL, true)), '==?', domain__debug(getDomain(indexO, true)));
    // an issame can only be leaf-cut on an arg if the leaf can represent all outcomes
    // so if C is solved, solve as SAME or DIFF.
    // otherwise make sure the leaf contains all vars of the other var and at least one var that's not in there
    // as long as that's impossible we can't cut it without implicitly forcing vars

    // first check whether R is booly-solved, this would mean fewer values to check

    let R = getDomain(indexR, true);
    if (domain_isZero(R)) {
      TRACE('    - R=0 and size(L)>2 so cuttable');
      // L contains at least two values so regardless of the state of O, L can fulfill !=
      ASSERT(domain_size(L) >= 2, 'see?');
      return true;
    }

    // R=1 or R=booly is more involved because we at least
    // need to know whether L contains all values in O

    let L = getDomain(indexL, true);
    let O = getDomain(indexO, true);
    let LO = domain_intersection(L, O); // <-- this tells us that
    TRACE('    - LO:', domain__debug(LO));

    if (domain_hasNoZero(R)) {
      // only cut if we are certain L can represent eq in any way O solves

      if (!LO) {
        TRACE('    - R>=1 and A contains no value in B so reject');
        // no values in L and O match so reject
        setDomain(indexL, domain_createEmpty(), false, true);
        return false;
      }

      if (LO === O) {
        TRACE('    - R>=1 and A contains all values in B so cuttable');
        // this means L contains all values in O (and maybe more, dont care)
        // which means L can uphold the eq for any value of O
        return true;
      }

      TRACE('    - R>=1 and A contains some but not all B so not cuttable, yet');
      // there's no guarantee O solves to a value in L so we cant cut safely
      return true;
    }

    TRACE('    - R unresolved, cuttable if L contains all values in O and then some;', LO === O, LO !== L, 'so:', LO === O && LO !== L);
    // we dont know R so L should contain all values in O (LO==O) and at least
    // one value not in O (LO != O), to consider this a safe cut. otherwise dont.
    return LO === O && LO !== L;
  }

  function cut_issome(ml, offset) {
    let argCount = ml_dec16(ml, offset + 1);
    let argsOffset = offset + SIZEOF_C;
    let opSize = SIZEOF_C + argCount * 2 + 2;

    let indexR = readIndex(ml, argsOffset + argCount * 2);
    let countsR = getCounts(bounty, indexR);

    TRACE(' ! cut_issome; R=', indexR);

    if (countsR === 1) {
      return leaf_issome(ml, offset, indexR, argCount);
    }

    for (let i = 0; i < argCount; ++i) {
      let index = readIndex(ml, offset + SIZEOF_C + i * 2);

      let A = getDomain(index, true);
      if (domain_isZero(A)) {
        TRACE(' - some has zeroes, requesting minimizer to remove them');
        requestAnotherCycle = true; // minimizer should eliminate these
        break;
      }
    }

    TRACE(' - cut_issome did not change anything');
    pc += opSize;
  }

  function cut_lt(ml, offset) {
    let indexA = readIndex(ml, offset + OFFSET_C_A);
    let indexB = readIndex(ml, offset + OFFSET_C_B);

    let countsA = getCounts(bounty, indexA);
    let countsB = getCounts(bounty, indexB);

    TRACE(' ! cut_lt; ', indexA, '<', indexB, '::', domain__debug(getDomain(indexA, true)), '<', domain__debug(getDomain(indexB, true)));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    TRACE('  - counts:', countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexA), '<', bounty__debugMeta(bounty, indexB));

    if (indexA === indexB) {
      TRACE(' - index A == B, redirecting to minimizer');
      requestAnotherCycle = true;
      return;
    }

    if (countsA === 1) {
      return leaf_lt(ml, offset, indexA, indexB, 'lhs');
    }

    if (countsB === 1) {
      return leaf_lt(ml, offset, indexA, indexB, 'rhs');
    }

    TRACE(' - cut_lt did not change anything');
    pc += SIZEOF_C_2;
  }

  function cut_lte(ml, offset) {
    let indexA = readIndex(ml, offset + OFFSET_C_A);
    let indexB = readIndex(ml, offset + OFFSET_C_B);

    let countsA = getCounts(bounty, indexA);
    let countsB = getCounts(bounty, indexB);

    TRACE(' ! cut_lte; ', indexA, '<=', indexB, '::', domain__debug(getDomain(indexA, true)), '<=', domain__debug(getDomain(indexB, true)));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    TRACE('  - counts:', countsA, '<=', countsB, ', meta:', bounty__debugMeta(bounty, indexA), '<=', bounty__debugMeta(bounty, indexB));

    if (indexA === indexB) {
      TRACE(' - index A == B, redirecting to minimizer');
      requestAnotherCycle = true;
      return;
    }

    if (countsA === 1) {
      if (leaf_lte(ml, offset, indexA, indexB, true)) return;
    }

    if (countsB === 1) {
      if (leaf_lte(ml, offset, indexA, indexB, false)) return;
    }

    if (countsA > 0) {
      let metaA = getMeta(bounty, indexA);

      if (metaA === BOUNTY_FLAG_NALL || metaA === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_LTE_LHS)) {
        if (trick_ltelhs_nall_leaf(ml, indexA, countsA)) return;
      }
      if (metaA === BOUNTY_FLAG_LTE_LHS) {
        if (trick_only_ltelhs_leaf(ml, indexA, countsA)) return;
      }

      if (countsA === 2) {
        if (metaA === (BOUNTY_FLAG_LTE_LHS | BOUNTY_FLAG_SOME)) {
          if (trick_ltelhs_some_leaf(ml, offset, indexA, countsA)) return;
        }
      }

      if (countsA >= 3) {
        if (metaA === (BOUNTY_FLAG_SOME | BOUNTY_FLAG_NALL | BOUNTY_FLAG_LTE_LHS)) {
          if (trick_ltelhs_nalls_some(indexA, countsA)) return;
        }
        if (metaA === (BOUNTY_FLAG_SOME | BOUNTY_FLAG_NALL | BOUNTY_FLAG_LTE_LHS | BOUNTY_FLAG_LTE_RHS)) {
          if (trick_lteboth_nall_some(indexA, countsA)) return;
        }
      }

      if (hasFlags(metaA, BOUNTY_FLAG_ISALL_RESULT)) {
        // in this trick one constraint subsumes the other so no need for A being a leaf
        if (trick_isall_ltelhs_2shared(ml, offset, indexA, countsA)) return;

        // in this trick A needs to be a leaf
        if (countsA === 2) {
          if (trick_isall_ltelhs_1shared(ml, offset, indexA, countsA)) return;
        }
      }
    }

    if (countsB === 2) {
      let metaB = getMeta(bounty, indexB);

      if (metaB === (BOUNTY_FLAG_LTE_RHS | BOUNTY_FLAG_ISALL_RESULT)) {
        if (trick_isall_lterhs_entry(indexB, offset, countsB)) return;
      }

      if (metaB === (BOUNTY_FLAG_LTE_RHS | BOUNTY_FLAG_ISSAME_RESULT)) {
        if (trick_issame_lterhs(indexB, offset, countsB, indexA)) return;
      }
    }

    TRACE(' - cut_lte changed nothing');
    pc += SIZEOF_C_2;
  }

  function cut_nall(ml, offset) {
    let argCount = ml_dec16(ml, offset + 1);

    TRACE(' ! cut_nall;', argCount, 'args');

    let indexA = readIndex(ml, offset + OFFSET_C_A);
    let countsA = getCounts(bounty, indexA);
    if (countsA > 1 && countsA < BOUNTY_MAX_OFFSETS_TO_TRACK) {
      // search all counts for a second SOME
      if (desubset_nall(ml, offset, argCount, indexA, countsA)) return;
    }

    if (argCount === 2) {
      if (readIndex(ml, offset + OFFSET_C_A) === readIndex(ml, offset + OFFSET_C_B)) {
        TRACE(' - argcount=2 and A==B, requesting minimzer cycle');
        requestAnotherCycle = true;
        return;
      }
    }

    for (let i = 0; i < argCount; ++i) {
      let index = readIndex(ml, offset + SIZEOF_C + i * 2);
      let counts = getCounts(bounty, index);

      if (counts > 0) {
        let meta = getMeta(bounty, index);
        if (meta === BOUNTY_FLAG_NALL) {
          // var is only used in nalls. eliminate them all and defer the var
          if (trickNallOnly(index, counts)) return true;
        }
      }
    }

    TRACE(' - cut_nall did not change anything');
    pc += SIZEOF_C + argCount * 2;
  }

  function cut_some(ml, offset) {
    let argCount = ml_dec16(ml, pc + 1);

    TRACE(' ! cut_some;', argCount, 'args');

    let indexA = readIndex(ml, offset + OFFSET_C_A);
    let countsA = getCounts(bounty, indexA);
    if (countsA > 1 && countsA < BOUNTY_MAX_OFFSETS_TO_TRACK) {
      // search all counts for a second SOME
      if (desubset_some(ml, offset, argCount, indexA, countsA)) return;
    }

    if (argCount === 2) {
      let indexB = readIndex(ml, offset + OFFSET_C_B);

      if (indexA === indexB) {
        TRACE(' - argcount=2 and A==B, requesting minimzer cycle');
        requestAnotherCycle = true;
        return;
      }

      if (countsA === 1) {
        leaf_some_2(ml, offset, indexA, indexB, indexA, indexB);
        return;
      }

      let countsB = getCounts(bounty, indexB);

      if (countsB === 1) {
        leaf_some_2(ml, offset, indexB, indexA, indexA, indexB);
        return;
      }
    }

    let hasZero = false;
    for (let i = 0; i < argCount; ++i) {
      let index = readIndex(ml, offset + SIZEOF_C + i * 2);
      let counts = getCounts(bounty, index);

      if (counts > 0) {
        let meta = getMeta(bounty, index);
        if (meta === BOUNTY_FLAG_SOME) {
          // var is only used in SOMEs. eliminate them all and defer the var
          if (trickSomeOnly(index, counts)) return true;
        }
      }

      let A = getDomain(index, true);
      if (domain_isZero(A)) {
        hasZero = true;
      }
    }

    if (hasZero) {
      TRACE(' - some has zeroes, requesting minimizer to remove them');
      requestAnotherCycle = true; // minimizer should eliminate these
    }

    TRACE(' - cut_some changed nothing');
    pc += SIZEOF_C + argCount * 2;
  }

  function cut_sum(ml, offset) {
    let argCount = ml_dec16(ml, offset + 1);
    let argsOffset = offset + SIZEOF_C;
    let opSize = SIZEOF_C + argCount * 2 + 2;

    let indexR = readIndex(ml, argsOffset + argCount * 2);
    let R = getDomain(indexR, true);
    let countsR = getCounts(bounty, indexR);

    TRACE(' ! cut_sum;');
    TRACE('  - index R:', indexR, ', domain:', domain__debug(R), ', argCount:', argCount, ',counts R:', countsR, ', meta R:', bounty__debugMeta(bounty, indexR));
    ASSERT(!countsR || !domain_isSolved(getDomain(indexR, true)), 'if it has counts it shouldnt be solved', countsR, indexR, domain__debug(getDomain(indexR, true)));

    let RisBoolyPair = domain_isBoolyPair(R);

    // collect meta data on the args of this sum
    // TODO: should we have a bounty for both constraints and vars?
    let allSumArgsBool = true; // all args [01]? used later
    let allSumArgsBoolyPairs = true; // all args have a zero and one nonzero value?
    let sum = domain_createValue(0);
    let argsMinSum = 0;
    let argsMaxSum = 0;
    let constantValue = 0; // allow up to one constant larger than 0
    let constantArgIndex = -1;
    let multiConstants = false;
    for (let i = 0; i < argCount; ++i) {
      let index = readIndex(ml, argsOffset + i * 2);
      let domain = getDomain(index, true);
      let minValue = domain_min(domain);
      let maxValue = domain_max(domain);

      sum = domain_plus(sum, domain);
      argsMinSum += minValue;
      argsMaxSum += maxValue;
      //let nonBoolNonSolvedDomain = maxValue > 1;
      if (minValue === maxValue) {
        multiConstants = constantArgIndex >= 0;
        constantValue = minValue;
        constantArgIndex = i;
      } else {
        if (!domain_isBoolyPair(domain)) allSumArgsBoolyPairs = false;
        if (!domain_isBool(domain)) allSumArgsBool = false;
      }
    }

    TRACE(' - sum args; min:', argsMinSum, ', max:', argsMaxSum, ', constantValue:', constantValue, ', constant pos:', constantArgIndex, ', sum:', domain__debug(sum));

    if (multiConstants) {
      TRACE(' - multiple constants detected, bailing so minimizer can correct this');
      return;
    }

    // [0 0 23 23] = [0 1] + [0 0 2 2] + [0 0 20 20]   ->    R = all?(A B C)
    if (RisBoolyPair && allSumArgsBoolyPairs) {
      // this trick is irrelevant of leaf status (this could be part of minimizer)
      TRACE(' - R is a booly and all the args are booly too, checking whether', domain_max(R), '===', argsMaxSum);
      ASSERT(argsMinSum === 0, 'if all are booly argsMinSum should be zero');
      if (domain_max(R) === argsMaxSum) {
        TRACE(' - R is', domain__debug(R), 'and all the args are booly and their argsMaxSum is equal to max(R) so this is actually an isall. morphing sum to isall');
        ml_enc8(ml, offset, ML_ISALL);
        return;
      }
    }

    // note: we cant simply eliminate leaf vars because they still constrain
    // the allowed distance between the other variables and if you
    // eliminate this constraint, that limitation is not enforced anymore.
    // so thread carefully.
    if (countsR === 1) {
      // R can only be eliminated if all possible additions between A and B occur in it
      // because in that case it no longer serves as a constraint to force certain distance(s)

      if (sum === domain_intersection(R, sum)) {
        // all possible outcomes of summing any element in the sum args are part of R so
        // R is a leaf and the args aren't bound by it so we can safely remove the sum
        return leaf_sum_result(ml, offset, argCount, indexR);
      }

      // if R is [0, n-1] and all n args are [0, 1] then rewrite to a NALL
      if (allSumArgsBool && R === domain_createRange(0, argCount - 1)) {
        return trick_sum_to_nall(ml, offset, argCount, indexR);
      }

      // if R is [1, n] and all n args are [0, 1] then rewrite to a SOME
      if (allSumArgsBool && R === domain_createRange(1, argCount)) {
        return trick_some_sum(ml, offset, argCount, indexR);
      }
    }

    if (countsR >= 2) {
      let metaR = getMeta(bounty, indexR);
      ASSERT(hasFlags(metaR, BOUNTY_FLAG_SUM_RESULT), 'per definition because this is the R in a sum');

      // TODO: cant we also do this with counts>2 when R is a bool when ignoring the sum?
      // TOFIX: confirm whether we need allSumArgsBool here, or whether we can lax it a little
      if (allSumArgsBoolyPairs && countsR === 2) {
        // we already confirmed that R is for a sum, so we can strictly compare the meta flags

        // (R = sum(A B C) & (S = R==?3)        ->    S = all?(A B C)
        // (R = sum(A B C) & (S = R==?0)        ->    S = none?(A B C)
        // (R = sum(A B C) & (S = R==?[0 1])    ->    S = nall?(A B C)
        // (R = sum(A B C) & (S = R==?[1 2])    ->    S = some?(A B C)
        if (metaR === (BOUNTY_FLAG_ISSAME_ARG | BOUNTY_FLAG_SUM_RESULT)) {
          if (trick_issame_sum(ml, offset, indexR, countsR, argCount, sum, argsMinSum, argsMaxSum, constantValue, constantArgIndex, allSumArgsBoolyPairs)) return;
        }

        // (R = sum(A B C) & (S = R!=?3)        ->    S = nall?(A B C)
        // (R = sum(A B C) & (S = R!=?0)        ->    S = some?(A B C)
        // (R = sum(A B C) & (S = R!=?[0 1])    ->    S = all?(A B C)
        // (R = sum(A B C) & (S = R!=?[1 2])    ->    S = none?(A B C)
        //if (metaR === (BOUNTY_FLAG_ISDIFF_ARG | BOUNTY_FLAG_SUM_RESULT)) {
        //  if (trickSumIsdiff(ml, offset, indexR, countsR)) return;
        //}

        // (R = sum(A B C) & (S = R<=?0)        ->    S = none?(A B C)
        // (R = sum(A B C) & (S = R<=?2)        ->    S = nall?(A B C)
        // (R = sum(A B C) & (S = 1<=?R)        ->    S = some?(A B C)
        // (R = sum(A B C) & (S = 3<=?R)        ->    S = all?(A B C)
        if (metaR === (BOUNTY_FLAG_ISLTE_ARG | BOUNTY_FLAG_SUM_RESULT)) {
          if (trick_islte_sum(ml, offset, indexR, countsR, argCount, argsMinSum, argsMaxSum, constantValue, constantArgIndex)) return;
        }

        // (R = sum(A B C) & (S = R<?1)        ->    S = none?(A B C)
        // (R = sum(A B C) & (S = R<?3)        ->    S = nall?(A B C)
        // (R = sum(A B C) & (S = 0<?R)        ->    S = some?(A B C)
        // (R = sum(A B C) & (S = 2<?R)        ->    S = all?(A B C)
        //if (metaR === (BOUNTY_FLAG_ISLT_ARG | BOUNTY_FLAG_SUM_RESULT)) {
        //  if (trickSumIslt(ml, offset, indexR, countsR)) return;
        //}
      }

      if (countsR === 3 && argCount === 2 && metaR === (BOUNTY_FLAG_ISSAME_ARG | BOUNTY_FLAG_SUM_RESULT)) { // TODO: make generic :)
        // R = sum(A B), S = R ==? 1, T = R ==? 2    ->    S = A !=? B, T = all?(A B)
        if (trick_issame_issame_sum(ml, offset, indexR, countsR, sum, argCount)) return;
      }

      if (countsR < BOUNTY_MAX_OFFSETS_TO_TRACK) {
        // if R is only used as a booly and (this) sum result, the actual result is irrelevant: only zero or not zero
        // in that case we only want to know whether any of its arguments are non-zero => `isSome`
        // For example: (R = sum(A B C), R ^ X) -> (R = isNone?(A B C), R ^ X)
        if (trick_sum_booly(ml, offset, indexR, countsR, sum, argCount)) return;
      }
    }

    TRACE(' - cut_sum changed nothing');
    pc += opSize;
  }

  function cut_xnor(ml, offset) {
    let argCount = ml_dec16(ml, offset + 1);

    TRACE(' ! cut_xnor;', argCount, 'args');

    if (argCount === 2) {
      let indexA = readIndex(ml, offset + OFFSET_C_A);
      let indexB = readIndex(ml, offset + OFFSET_C_B);

      let countsA = getCounts(bounty, indexA);
      let countsB = getCounts(bounty, indexB);

      TRACE(' - 2 args!', indexA, '!^', indexB, '::', domain__debug(getDomain(indexA, true)), '!^', domain__debug(getDomain(indexB, true)));
      ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
      ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
      TRACE('  - counts:', countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexA), '!^', bounty__debugMeta(bounty, indexB));

      if (indexA === indexB) {
        TRACE(' - argcount=2 and A==B, requesting minimzer cycle');
        requestAnotherCycle = true;
        return;
      }

      if (countsA === 1) {
        return leaf_xnor(ml, offset, indexA, indexB, indexA, indexB);
      }

      if (countsB === 1) {
        return leaf_xnor(ml, offset, indexB, indexA, indexA, indexB);
      }

      // (do we care about constants here? technically the minimizer should eliminate xnors with constants... so, no?)
      if (countsA > 0 && countsB > 0) {
        let metaA = getMeta(bounty, indexA, true); // keep booly flags
        let metaB = getMeta(bounty, indexB, true);
        TRACE(' - considering whether A and B are xnor pseudo aliases;', bounty__debugMeta(bounty, indexA), '!^', bounty__debugMeta(bounty, indexB));
        let boolyA = !hasFlags(metaA, BOUNTY_FLAG_NOT_BOOLY);
        let boolyB = !hasFlags(metaB, BOUNTY_FLAG_NOT_BOOLY);
        TRACE(' - ', (boolyA || boolyB) ? 'yes' : 'no', ' ->', boolyA, '||', boolyB);
        if (boolyA || boolyB) {
          // we declare A and alias of B. they are both used as booly only and the xnor states that if and
          // only if A is truthy then B must be truthy too. since we confirmed both are only used as booly
          // their actual non-zero values are irrelevant and the rewrite is safe. the last thing to make
          // sure is that the domains are updated afterwards and not synced and clobbered by the alias code.
          return trick_xnor_pseudoSame(ml, offset, indexA, boolyA, indexB, boolyB);
        }
      }
    }

    TRACE(' - cut_xnor did nothing');
    pc += SIZEOF_C + argCount * 2;
  }

  function cut_xor(ml, offset) {
    let indexA = readIndex(ml, offset + OFFSET_C_A);
    let indexB = readIndex(ml, offset + OFFSET_C_B);

    let countsA = getCounts(bounty, indexA);
    let countsB = getCounts(bounty, indexB);

    TRACE(' ! cut_xor; ', indexA, '^', indexB, '::', domain__debug(getDomain(indexA, true)), '^', domain__debug(getDomain(indexB, true)));
    TRACE('  - counts:', countsA, countsB, ', meta:', bounty__debugMeta(bounty, indexA), '^', bounty__debugMeta(bounty, indexB));
    ASSERT(!countsA || !domain_isSolved(getDomain(indexA, true)), 'if it has counts it shouldnt be solved', countsA, indexA, domain__debug(getDomain(indexA, true)));
    ASSERT(!countsB || !domain_isSolved(getDomain(indexB, true)), 'if it has counts it shouldnt be solved', countsB, indexB, domain__debug(getDomain(indexB, true)));
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'xor always has 2 args');

    if (indexA === indexB) {
      TRACE(' - argcount=2 and A==B, requesting minimzer cycle');
      requestAnotherCycle = true;
      return;
    }

    if (countsA === 1) {
      return leaf_xor(ml, offset, indexA, indexB, indexA, indexB);
    }

    if (countsB === 1) {
      return leaf_xor(ml, offset, indexB, indexA, indexA, indexB);
    }

    let A = getDomain(indexA, true);
    let B = getDomain(indexB, true);
    if (!domain_isBooly(A) || !domain_isBooly(B)) {
      TRACE(' / at least A or B is already booly solved. bailing so minimizer can take over.');
      requestAnotherCycle = true;
      return;
    }

    if (countsA > 0 && countsB > 0) {
      let metaA = getMeta(bounty, indexA, true); // keep booly flags
      let metaB = getMeta(bounty, indexB, true);

      let AonlyUsedBooly = !hasFlags(metaA, BOUNTY_FLAG_NOT_BOOLY);
      let BonlyUsedBooly = !hasFlags(metaB, BOUNTY_FLAG_NOT_BOOLY);

      // meta should only be these flags
      let TRICK_INV_XOR_FLAGS = BOUNTY_FLAG_SOME | BOUNTY_FLAG_NALL | BOUNTY_FLAG_IMP_LHS | BOUNTY_FLAG_IMP_RHS | BOUNTY_FLAG_XOR;

      if (countsA < BOUNTY_MAX_OFFSETS_TO_TRACK) {
        // check for some/nall/imp/xor. if A only concerns these then we can invert those
        // ops and remove the xor. Note: LTE only works when it could be an implication,
        // so we can omit a check for that as those LTE's should morph into IMP eventually
        TRACE('  - A; only contains good flags?', (metaA & TRICK_INV_XOR_FLAGS) === metaA);
        if ((metaA & TRICK_INV_XOR_FLAGS) === metaA) {
          if (trick_xor_elimination(offset, indexA, countsA, indexB)) return;
        }

        if (countsA === 2) {
          if (hasFlags(metaA, BOUNTY_FLAG_ISALL_RESULT)) {
            // R^A, R=all?(X Y Z)  ->   A=nall(X Y Z)
            if (trick_isall_xor(indexA, indexB, offset, countsA, countsB)) return;
          }

          if (AonlyUsedBooly && hasFlags(metaA, BOUNTY_FLAG_ISSOME_RESULT)) {
            // R^X, R=some?(A B C)   ->    X=none?(A B C)
            if (trick_issome_xor(indexA, indexB, offset, countsA, countsB)) return;
          }

          if (metaA === (BOUNTY_FLAG_XOR | BOUNTY_FLAG_SOME)) {
            if (trick_some_xor(indexA, indexB, offset, countsA)) return;
          }
        }

        let sB = domain_size(B);
        if (trick_xor_alias(indexA, indexB, countsA, B, sB, BonlyUsedBooly)) return;
      }

      if (countsB < BOUNTY_MAX_OFFSETS_TO_TRACK) {
        // check for some/nall/imp/xor. if B only concerns these then we can invert those
        // ops and remove the xor. Note: LTE only works when it could be an implication,
        // so we can omit a check for that as those LTE's should morph into IMP eventually
        TRACE('  - B; only contains good flags?', (metaB & TRICK_INV_XOR_FLAGS) === metaB);
        if (domain_isBoolyPair(B) && (metaB & TRICK_INV_XOR_FLAGS) === metaB) {
          if (trick_xor_elimination(offset, indexB, countsB, indexA)) return;
        }

        if (countsB === 2) {
          if (hasFlags(metaB, BOUNTY_FLAG_ISALL_RESULT)) {
            // R^B, R=all?(X Y Z)  ->   B=nall(X Y Z)
            if (trick_isall_xor(indexB, indexA, offset, countsB, countsA)) return;
          }

          if (BonlyUsedBooly && hasFlags(metaB, BOUNTY_FLAG_ISSOME_RESULT)) {
            // R^X, R=some?(A B C)   ->    X=none?(A B C)
            if (trick_issome_xor(indexB, indexA, offset, countsB, countsA)) return;
          }

          if (metaB === (BOUNTY_FLAG_XOR | BOUNTY_FLAG_SOME)) {
            if (trick_some_xor(indexB, indexA, offset, countsB)) return;
          }
        }

        let sA = domain_size(A);
        if (trick_xor_alias(indexB, indexA, countsB, A, sA, AonlyUsedBooly)) return;
      }
    }

    TRACE(' / cut_xor changed nothing');
    pc += SIZEOF_C_2;
  }

  // ##############

  function leaf_diff_pair(ml, offset, leafIndex, otherIndex, indexA, indexB) {
    TRACE('   - leaf_diff_pair;', leafIndex, 'is a leaf var, A != B,', indexA, '!=', indexB);

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_diff_pair; solving', indexA, '!=', indexB, '  ->  ', domain__debug(getDomain(indexA)), '!=', domain__debug(getDomain(indexB)));

      let A = getDomain(indexA);
      let B = getDomain(indexB);
      if (domain_size(A) < domain_size(B)) {
        let v = force(indexA);
        setDomain(indexB, domain_removeValue(B, v));
      } else {
        let v = force(indexB);
        setDomain(indexA, domain_removeValue(A, v));
      }
      ASSERT(getDomain(indexA) !== getDomain(indexB), 'D ought to have at least a value other dan v');
    });

    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, leafIndex);
    bounty_markVar(bounty, otherIndex);
    somethingChanged();
  }

  function leaf_imp(ml, offset, indexA, indexB, leafIsA) {
    TRACE('   - leaf_imp;', leafIsA ? 'A' : 'B', 'is a leaf var, A -> B;', indexA, '->', indexB);
    ASSERT(typeof indexA === 'number', 'index A should be number', indexA);
    ASSERT(typeof indexB === 'number', 'index B should be number', indexB);

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_imp; solving', indexA, '->', indexB, '  =>  ', domain__debug(getDomain(indexA)), '->', domain__debug(getDomain(indexB)), '  =>  ', domain_max(getDomain(indexA)), '->', domain_min(getDomain(indexB)));

      let A = getDomain(indexA);
      let B = getDomain(indexB);

      // TODO: weigh in value dists here

      if (leafIsA) {
        TRACE(' - A was leaf; A=', domain__debug(A), '->', domain__debug(B));
        // (we could simply and safely set A to 0 here and skip the solvestack part completely)
        if (domain_hasNoZero(B)) {
          let nA = domain_removeValue(A, 0);
          ASSERT(nA, 'A should not be empty');
          if (A !== nA) setDomain(indexA, nA);
        } else {
          let nA = domain_intersectionValue(A, 0);
          ASSERT(nA, 'A should not be empty');
          if (A !== nA) setDomain(indexA, nA);
        }
      } else {
        TRACE(' - B was leaf; A=', domain__debug(A), '->', domain__debug(B));
        // (we could simply and safely set B to nonzero here and skip the solvestack part completely)
        if (domain_hasNoZero(A)) {
          let nB = domain_removeValue(B, 0);
          ASSERT(nB, 'B should not be empty');
          if (A !== nB) setDomain(indexB, nB);
        } else {
          let nB = domain_intersectionValue(B, 0);
          ASSERT(nB, 'B should not be empty');
          if (B !== nB) setDomain(indexB, nB);
        }
      }
    });

    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    somethingChanged();
  }

  function leaf_isdiff(ml, offset, indexA, indexB, indexR, indexL) {
    TRACE('   - leaf_isdiff; index', indexL, 'is a leaf var, R = A !=? B,', indexR, '=', indexA, '!=?', indexB, '  ->  ', domain__debug(getDomain(indexR)), '=', domain__debug(getDomain(indexA)), '!=?', domain__debug(getDomain(indexB)));

    ASSERT(ml_dec16(ml, offset + 1) === 2);

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_isdiff');

      let A = getDomain(indexA);
      let B = getDomain(indexB);
      let R = getDomain(indexR);
      TRACE(' - leaf=', indexL, ';', indexR, '=', indexA, '!=?', indexB, '  =>  ', domain__debug(R), '=', domain__debug(A), '!=?', domain__debug(B), ', AB=', domain__debug(domain_intersection(A, B)));

      if (domain_isSolved(A)) {
        if (domain_isSolved(B)) {
          TRACE(' - A and B are solved, set R to reflect', domain_getValue(A), '!=', domain_getValue(B));
          if (A !== B) R = domain_removeValue(R, 0);
          else R = domain_removeGtUnsafe(R, 0);
          setDomain(indexR, R);
        } else if (domain_isBooly(R)) {
          TRACE(' - A is solved but B and R arent, remove A from B and set R>0');
          B = domain_removeValue(B, domain_getValue(A));
          setDomain(indexB, B);
          R = domain_removeValue(R, 0);
          setDomain(indexR, R);
        } else {
          TRACE(' - A and R are solved, set B to reflect it');
          if (domain_isZero(R)) {
            TRACE(' - R=0 so A==B');
            setDomain(indexB, A);
          } else {
            TRACE(' - R>0 so A!=B');
            B = domain_removeValue(B, domain_getValue(A));
            setDomain(indexB, B);
          }
        }
      } else if (domain_isSolved(B)) {
        if (domain_isBooly(R)) {
          TRACE(' - B is solved but A and R are not. Remove B from A and set R>0');
          A = domain_removeValue(A, domain_getValue(B));
          setDomain(indexA, A);
          R = domain_removeValue(R, 0);
          setDomain(indexR, R);
        } else {
          TRACE(' - B and R are solved but A is not. Update A to reflect R');
          if (domain_isZero(R)) {
            TRACE(' - R=0 so A==B');
            setDomain(indexA, B);
          } else {
            TRACE(' - R>0 so A!=B');
            A = domain_removeValue(A, domain_getValue(B));
            setDomain(indexA, A);
          }
        }
      } else if (domain_isBooly(R)) {
        TRACE(' - A, B, and R arent solved. force A and remove it from B (if A and B intersect) and set R>0');
        if (domain_intersection(A, B) !== EMPTY) {
          B = domain_removeValue(B, force(indexA));
          setDomain(indexB, B);
        }
        R = domain_removeValue(R, 0);
        setDomain(indexR, R);
      } else {
        TRACE(' - A and B arent solved but R is. update A and B to reflect R');
        if (domain_isZero(R)) {
          TRACE(' - R=0 so A==B');
          let vA = force(indexA, domain_intersection(A, B));
          ASSERT(domain_intersection(B, domain_createValue(vA)) !== EMPTY);
          B = domain_createValue(vA);
          setDomain(indexB, B);
        } else {
          let vA = force(indexA);
          B = domain_removeValue(B, vA);
          setDomain(indexB, B);
        }
      }

      TRACE(' - afterwards: R:' + indexR + ':' + domain__debug(getDomain(indexR)), ' = A:' + indexA + ':' + domain__debug(getDomain(indexA)), ' !=? B:' + indexB + ':' + domain__debug(getDomain(indexB)), ', AB=', domain__debug(domain_intersection(getDomain(indexA), getDomain(indexB))));

      // 3 things must hold;
      // - A or B must be solved or not intersect (otherwise future reductions may violate R)
      // - R must not be booly (obviously)
      // - R's state must reflect whether or not A shares a value with B (which by the above should at most be one value, but that's not helpful)
      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexB));
      ASSERT(getDomain(indexR));
      ASSERT(domain_intersection(getDomain(indexA), getDomain(indexB)) === EMPTY || domain_isSolved(getDomain(indexA)) || domain_isSolved(getDomain(indexB)), 'at least A or B must be solved in order to ensure R always holds');
      ASSERT(!domain_isBooly(getDomain(indexR)), 'R must not be a booly to ensure the constraint always holds');
      ASSERT((domain_intersection(getDomain(indexA), getDomain(indexB)) === EMPTY) === domain_hasNoZero(getDomain(indexR)), 'R must be nonzero if A and B share no elements');
    });

    ASSERT(ml_dec16(ml, offset + 1) === 2, 'argcount should be 2 at the moment');
    ml_eliminate(ml, offset, SIZEOF_CR_2);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    somethingChanged();
  }

  function leaf_isall(ml, offset, argCount, indexR) {
    TRACE('   - leaf_isall;', indexR, 'is a leaf var, R = all?(', argCount, 'x ),', indexR, '= all?(...)');

    let args = markAndCollectArgs(ml, offset, argCount);

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_isall; ', indexR, '= isAll(', args.join(' '), ')  ->  ', domain__debug(getDomain(indexR)), ' = isAll(', args.map(index => domain__debug(getDomain(index))).join(' '), ')');
      let vR = 1;
      for (let i = 0; i < argCount; ++i) {
        if (force(args[i]) === 0) {
          vR = 0;
          break;
        }
      }
      let oR = getDomain(indexR);
      let R = domain_resolveAsBooly(oR, vR);
      ASSERT(R, 'R should be able to at least represent the solution');
      setDomain(indexR, R);
    });

    ml_eliminate(ml, offset, SIZEOF_C + argCount * 2 + 2);
    bounty_markVar(bounty, indexR);
    somethingChanged();
  }

  function leaf_isall_arg_result(ml, indexR, countsR) {
    // R is only result or arg of isall ops.
    // for trick R must be result _and_ arg in _all_ the isalls

    // if R is only part of `R = all?(R ...)` ops then leaf(R) and eliminate the constraint
    // if R is part of `R = all?(R ...)` and `S = all?(R ...)` then leaf R and morph to imps S->A, S->B all other args


    let R = getDomain(indexR, true);
    if (!domain_isBool(R)) {
      TRACE(' - R is not bool, bailing');
      return false;
    }

    // first verify, scan, and collect
    let argOnlyOffsets = [];
    let resultOnlyOffsets = [];
    let argAndResultOffsets = [];
    let allArgs = [];
    let offsets = [];
    for (let i = 0; i < countsR; ++i) {
      let offset = bounty_getOffset(bounty, indexR, i);
      TRACE('    - i=', i, ', offset=', offset);
      ASSERT(ml_dec8(ml, offset) === ML_ISALL);
      // each offset could be visited twice if this trick is applied
      if (offsets.indexOf(offset) < 0) {
        let argCount = ml_dec16(ml, offset + 1);

        let resultIndex = readIndex(ml, offset + SIZEOF_C + argCount * 2);

        let args = [];
        let foundAsArg = false;
        for (let j = 0; j < argCount; ++j) {
          let index = readIndex(ml, offset + SIZEOF_C + j * 2);
          args.push(index);
          if (index === indexR) foundAsArg = true;
        }

        TRACE('    - is result?', resultIndex === indexR, ', is arg?', foundAsArg);

        ASSERT(foundAsArg || resultIndex === indexR, 'R should be part of the isall as per bounty');
        if (resultIndex !== indexR) argOnlyOffsets.push(offset);
        else if (!foundAsArg) resultOnlyOffsets.push(offset);
        else argAndResultOffsets.push(offset);

        allArgs.push(args);
        offsets.push(offset);
      }
    }

    TRACE(' - collected: result only:', resultOnlyOffsets, ', arg only:', argOnlyOffsets, ', both result and arg:', argAndResultOffsets);

    // three cases: either R was a result-only or arg-only in at least one isall, or not. yes, three cases.

    if (resultOnlyOffsets.length) {
      TRACE(' - there was at least one isall where R was the result only. cant apply this trick. bailing');
      return false;
    }

    ASSERT(argAndResultOffsets.length, 'bounty found R to be result and arg of isall and there were no isalls where R was result only so there must be at least one isall with R being result and arg');

    // two cases left: either R was result AND arg in all isalls or there was at least one isall where it was arg only

    if (argOnlyOffsets.length) {
      return _leafIsallArgResultMaybe(ml, indexR, allArgs, offsets, R, countsR, argOnlyOffsets, argAndResultOffsets);
    } else {
      return _leafIsallArgResultOnly(ml, indexR, allArgs, offsets, R);
    }
  }
  function _leafIsallArgResultMaybe(ml, indexR, allArgs, offsets, R, countsR, argOnlyOffsets, argAndResultOffsets) {
    TRACE(' - confirmed, R is only part of isall where R is result and arg or just arg and at least one of each');
    TRACE(' - R = all?(R ...), S = all?(R ...)    =>    S -> A, S -> B, ... for all args of the isalls');

    // note: one isall contributes 2 counts, the other only 1
    if (countsR !== 3) {
      TRACE(' - countsR != 3, for now we bail on this. maybe in the future we can do this.');
      return false;
    }

    ASSERT(argOnlyOffsets.length === 1 && argAndResultOffsets.length === 1, 'for now');

    let argOnlyIsallOffset = argOnlyOffsets[0];
    let argOnlyIsallArgCount = ml_dec16(ml, argOnlyIsallOffset + 1);

    let argAndResultIsallOffset = argAndResultOffsets[0];
    let argAndResultIsallArgCount = ml_dec16(ml, argAndResultIsallOffset + 1);

    let indexS = readIndex(ml, argOnlyIsallOffset + SIZEOF_C + argOnlyIsallArgCount * 2);
    if (argOnlyIsallArgCount !== 2 || argAndResultIsallArgCount !== 2) {
      let ok = _leafIsallArgResultExcess(ml, indexR, indexS, allArgs);
      if (!ok) return false;
    }

    let indexA = readIndex(ml, argOnlyIsallOffset + OFFSET_C_A);
    if (indexA === indexR) indexA = readIndex(ml, argOnlyIsallOffset + OFFSET_C_B);

    let indexB = readIndex(ml, argAndResultIsallOffset + OFFSET_C_A);
    if (indexB === indexR) indexB = readIndex(ml, argAndResultIsallOffset + OFFSET_C_B);

    TRACE_MORPH('R = all?(R A), S = all?(R B)', 'S -> A, S -> B', 'when R is leaf');
    TRACE(' - indexes;', indexR, '= all?(', indexR, indexA, '),', indexS, '= all?(', indexR, indexB, ')');
    TRACE(' - domains;', domain__debug(getDomain(indexR)), '= all?(', domain__debug(getDomain(indexR)), domain__debug(getDomain(indexA)), '),', domain__debug(getDomain(indexS)), '= all?(', domain__debug(getDomain(indexR)), indexB, ')');

    ml_cr2c2(ml, argOnlyIsallOffset, argOnlyIsallOffset, ML_IMP, indexS, indexA);
    ml_cr2c2(ml, argAndResultIsallOffset, argAndResultIsallOffset, ML_IMP, indexS, indexB);

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE('_leafIsallArgResultMaybe');

      let R = getDomain(indexR);
      let nR = R;

      // R = R &? A
      if (force(indexA) === 0) {
        TRACE(' - A is 0 so R cant be 1');
        nR = domain_removeGtUnsafe(nR, 0);
      } else {
        // S = R &? B
        let vS = force(indexS);
        if (vS) {
          TRACE(' - S>0 so R must be nonzero');
          nR = domain_removeValue(nR, 0);
        } else {
          ASSERT(vS === 0);
          if (force(indexB) > 0) {
            TRACE(' - S=0 and B>0 so R must be zero');
            nR = domain_removeGtUnsafe(nR, 0);
          }
        }
      }
      TRACE(' - final R:', domain__debug(nR));
      ASSERT(nR);
      if (R !== nR) setDomain(indexR, nR);
    });

    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    bounty_markVar(bounty, indexS);
    somethingChanged();

    return true;
  }
  function _leafIsallArgResultExcess(ml, indexR, indexS, argsPerIsall) {
    TRACE(' - _leafIsallArgResultExcess');

    TRACE(' - collecting excess args now; indexR:', indexR, ', all args:', argsPerIsall);
    // collect all args except indexR and the first arg of the first two isalls, or second if first is indexR
    // we need to recycle spaces for that
    let toCompile = [];
    for (let i = 0; i < argsPerIsall.length; ++i) {
      let args = argsPerIsall[i];
      TRACE('   -', i, '; isall args:', args);
      let gotOne = i >= 2;
      for (let j = 0; j < args.length; ++j) {
        let index = args[j];
        TRACE('     -', j, '; index:', index, index === indexR);
        if (index !== indexR) {
          if (!gotOne && j < 2) {
            TRACE('       - skipped (compiled by caller)');
            // skip the first non-R for the first two isalls
            gotOne = true;
          } else {
            TRACE('       - collected');
            toCompile.push(index);
          }
        }
      }
    }

    TRACE(' - excess args to compile in recycled spaces:', toCompile);

    // there could potentially be no args to compile here. and that's okay.
    let count = toCompile.length;
    if (count) {
      TRACE(' - found', count, 'extra args to compile:', toCompile);
      // start by collecting count recycled spaces
      let bins = ml_getRecycleOffsets(ml, 0, count, SIZEOF_C_2);
      if (!bins) {
        TRACE(' - Was unable to find enough free space to fit', count, 'IMPs, bailing');
        return false;
      }

      let i = 0;
      while (i < count) {
        let currentOffset = bins.pop();
        ASSERT(ml_dec8(ml, currentOffset) === ML_JMP, 'should only get jumps here'); // might trap a case where we clobber
        let size = ml_getOpSizeSlow(ml, currentOffset);
        ASSERT(size >= SIZEOF_C_2, 'this is what we asked for');
        do {
          let index = toCompile[i];
          TRACE('  - compiling lte:', indexS, '->', index, '   =>    ', domain__debug(getDomain(indexS, true)), '->', domain__debug(getDomain(index, true)));

          ml_any2c(ml, currentOffset, ml_getOpSizeSlow(ml, currentOffset), ML_IMP, [indexS, index]);

          ++i;
          size -= SIZEOF_C_2;
          currentOffset += SIZEOF_C_2;
        } while (size >= SIZEOF_C_2 && i < count);
        ASSERT(!void ml_validateSkeleton(ml), '_leafIsallArgResultExcess compiling ltes'); // cant check earlier
      }
      TRACE(' - finished compiling extra args');
    }

    return true;
  }
  function _leafIsallArgResultOnly(ml, indexR, allArgs, offsets, R) {
    TRACE(' - confirmed, all isalls have R as result _and_ arg; args:', allArgs, ', offsets:', offsets);
    TRACE(' - R is a leaf and we eliminate all isalls associated to R');

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_isall_arg_result');

      ASSERT(domain_isBool(R), 'R was a bool (asserted above, and as leaf, that should not have changed)');
      ASSERT(domain_isBool(getDomain(indexR)));

      // if all args besides R are set, then R can be anything. otherwise R is 0.
      // need to check this for all isalls. if any one causes R to be 0 then that's that.

      let allSet = true;
      for (let i = 0, len = allArgs.length; i < len; ++i) {
        let args = allArgs[i];
        for (let j = 0, len2 = args.length; j < len2; ++j) {
          let index = args[j];
          if (index !== indexR) {
            let D = getDomain(index);
            if (!domain_hasNoZero(D)) {
              allSet = false; // either it's zero or booly, either way set R to 0 and be done.
            }
          }
        }
        if (!allSet) {
          TRACE(' - foundAsArg an isall where not all other args were set so forcing R to 0');
          // remember: R is a bool, asserted above. twice now. so this cant possibly fail. (watch it fail. sorry, future me!)
          setDomain(indexR, domain_createValue(0));
          break;
        }
      }
      // otherwise R kind of determines itself so no choice is made :)
      TRACE(' - was R forced to 0?', !allSet);
    });

    TRACE(' - now marking vars and eliminating isall constraints');

    for (let i = 0, len = offsets.length; i < len; ++i) {
      let offset = offsets[i];
      let args = allArgs[i];
      TRACE('    - i=', i, ', offset=', offset, ', args=', args);
      TRACE_MORPH('R = all?(R ...)', '', 'if R only touches isalls on result _and_ arg then R is still a leaf');
      ASSERT(args.length === ml_dec16(ml, offset + 1), 'should be able to use this shortcut (not sure whether its actually faster tho)');
      ml_eliminate(ml, offset, SIZEOF_C + args.length * 2 + 2);
      for (let j = 0, len2 = args.length; j < len2; ++j) {
        TRACE('      - marking', args[j]);
        bounty_markVar(bounty, args[j]);
      }
    }

    somethingChanged();

    return true;
  }

  function leaf_islt(ml, offset, indexA, indexB, indexR, indexL) {
    TRACE('   - leaf_islt;', indexL, 'is a leaf var, R = A <? B,', indexR, '=', indexA, '<?', indexB, '  ->  ', domain__debug(getDomain(indexR)), '=', domain__debug(getDomain(indexA)), '<?', domain__debug(getDomain(indexB)));

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_islt');
      TRACE(' - leaf index=', indexL, ';', indexR, '=', indexA, '<?', indexB, '  ->  ', domain__debug(getDomain(indexR)), '=', domain__debug(getDomain(indexA)), '<?', domain__debug(getDomain(indexB)));

      let A = getDomain(indexA);
      let B = getDomain(indexB);
      let R = getDomain(indexR);

      // R doesnt need to be booly...
      if (domain_isBooly(R)) {
        TRACE(' - R is booly, just force A and B and reflect the result in R');
        let vA = force(indexA);
        let vB = force(indexB);
        if (vA < vB) R = domain_removeValue(R, 0);
        else R = domain_removeGtUnsafe(R, 0);
        setDomain(indexR, R);
      } else if (domain_isZero(R)) {
        TRACE(' - R=0 so force A>=B by setting A=maxA() and B=min(B)');

        // there are complexities with edge cases so for now just take the easy road;
        // assuming the problem was always solveable before; max(A) >= min(B)

        A = domain_createValue(domain_max(A));
        B = domain_createValue(domain_min(B));
        TRACE('   - now ==>', domain__debug(A), '>=', domain__debug(B));

        setDomain(indexA, A);
        setDomain(indexB, B);
      } else {
        ASSERT(domain_hasNoZero(R));
        TRACE(' - R>0 so force A<B ==>', domain__debug(A), '<', domain__debug(B));

        // there are complexities with edge cases so for now just take the easy road;
        // assuming the problem was always solveable before; min(A) < max(B)

        A = domain_createValue(domain_min(A));
        B = domain_createValue(domain_max(B));
        TRACE('   - now ==>', domain__debug(A), '>=', domain__debug(B));

        setDomain(indexA, A);
        setDomain(indexB, B);
      }

      TRACE(' - R:', domain__debug(getDomain(indexR)), '= A:', domain__debug(getDomain(indexA)), '< B:', domain__debug(getDomain(indexB)));

      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexB));
      ASSERT(getDomain(indexR));
      ASSERT(!domain_isBooly(getDomain(indexR)));
      ASSERT(!domain_isZero(getDomain(indexR)) === (domain_max(getDomain(indexA)) < domain_min(getDomain(indexB))), 'should hold constraint');
    });

    ml_eliminate(ml, offset, SIZEOF_VVV);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    somethingChanged();
  }

  function leaf_islte(ml, offset, indexA, indexB, indexR, indexL) {
    TRACE('   - leaf_islte;', indexL, 'is a leaf var, R = A <=? B,', indexR, '=', indexA, '<=?', indexB, '  ->  ', domain__debug(getDomain(indexR)), '=', domain__debug(getDomain(indexA)), '<=?', domain__debug(getDomain(indexB)));

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_islte');
      TRACE(' - leaf index=', indexL, ';', indexR, '=', indexA, '<=?', indexB, '  ->  ', domain__debug(getDomain(indexR)), '=', domain__debug(getDomain(indexA)), '<=?', domain__debug(getDomain(indexB)));

      let A = getDomain(indexA);
      let B = getDomain(indexB);
      let R = getDomain(indexR);

      // R doesnt need to be booly...
      if (domain_isBooly(R)) {
        TRACE(' - R is booly, just force A and B and reflect the result in R');
        let vA = force(indexA);
        let vB = force(indexB);
        if (vA <= vB) R = domain_removeValue(R, 0);
        else R = domain_removeGtUnsafe(R, 0);
        setDomain(indexR, R);
      } else if (domain_isZero(R)) {
        TRACE(' - R=0 so force A>=B by setting A=maxA() and B=min(B)');

        // there are complexities with edge cases so for now just take the easy road;
        // assuming the problem was always solveable before; max(A) > min(B)

        A = domain_createValue(domain_max(A));
        B = domain_createValue(domain_min(B));
        TRACE('   - now ==>', domain__debug(A), '>', domain__debug(B));

        setDomain(indexA, A);
        setDomain(indexB, B);
      } else {
        ASSERT(domain_hasNoZero(R));
        TRACE(' - R>0 so force A<=B ==>', domain__debug(A), '<=', domain__debug(B));

        // there are complexities with edge cases so for now just take the easy road;
        // assuming the problem was always solveable before; min(A) <= max(B)

        A = domain_createValue(domain_min(A));
        B = domain_createValue(domain_max(B));
        TRACE('   - now ==>', domain__debug(A), '<=', domain__debug(B));

        setDomain(indexA, A);
        setDomain(indexB, B);
      }

      TRACE(' - R:', domain__debug(getDomain(indexR)), '= A:', domain__debug(getDomain(indexA)), '<= B:', domain__debug(getDomain(indexB)));

      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexB));
      ASSERT(getDomain(indexR));
      ASSERT(!domain_isBooly(getDomain(indexR)));
      ASSERT(!domain_isZero(getDomain(indexR)) === (domain_max(getDomain(indexA)) <= domain_min(getDomain(indexB))), 'should hold constraint');
    });

    ml_eliminate(ml, offset, SIZEOF_VVV);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    somethingChanged();
  }

  function leaf_isnall(ml, offset, argCount, indexR, counts) {
    TRACE('   - leaf_isnall;', indexR, 'is a leaf var with counts:', counts, ', R = nall?(', argCount, 'x ),', indexR, '= all?(...)');

    let args = markAndCollectArgs(ml, offset, argCount);

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_isnall');
      TRACE('-', indexR, '= nall?(', args, ')  ->  ', domain__debug(getDomain(indexR)), ' = nall?(', args.map(index => domain__debug(getDomain(index))), ')');
      let vR = 0;
      for (let i = 0; i < argCount; ++i) {
        if (force(args[i]) === 0) {
          TRACE(' - found at least one arg that is zero so R>0');
          vR = 1;
          break;
        }
      }
      let oR = getDomain(indexR);
      let R = domain_resolveAsBooly(oR, vR);
      setDomain(indexR, R);

      ASSERT(getDomain(indexR));
      ASSERT(domain_hasNoZero(getDomain(indexR)) === args.some(index => domain_isZero(getDomain(index))));
    });

    ml_eliminate(ml, offset, SIZEOF_C + argCount * 2 + 2);
    bounty_markVar(bounty, indexR);
    somethingChanged();
  }

  function leaf_issame(ml, offset, indexA, indexB, indexR, indexL) {
    TRACE('   - leaf_issame; index', indexL, 'is a leaf var, R = A ==? B,', indexR, '=', indexA, '==?', indexB, '  ->  ', domain__debug(getDomain(indexR)), '=', domain__debug(getDomain(indexA)), '==?', domain__debug(getDomain(indexB)));
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'for now argcount should be 2');

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_issame; leaf=', indexL, ';', indexR, '=', indexA, '==?', indexB, '  ->  ', domain__debug(getDomain(indexR)), '=', domain__debug(getDomain(indexA)), '==?', domain__debug(getDomain(indexB)));

      let A = getDomain(indexA);
      let B = getDomain(indexB);
      let AB = domain_intersection(A, B);
      let R = getDomain(indexR);
      TRACE(' - A:', domain__debug(A), ', B:', domain__debug(B), ', AB:', domain__debug(AB), ', solved?', domain_isSolved(A), domain_isSolved(B));
      if (!domain_isSolved(R)) {
        if (!AB) {
          TRACE('   - A&B is empty so R=0');
          R = domain_resolveAsBooly(R, false);
        } else if (domain_isSolved(A)) {
          TRACE('   - A is solved so R=A==B', A === B);
          R = domain_resolveAsBooly(R, A === B);
        } else if (domain_isSolved(B)) {
          TRACE('   - B is solved and A wasnt. A&B wasnt empty so we can set A=B');
          setDomain(indexA, B);
          R = domain_resolveAsBooly(R, true);
        } else {
          TRACE('   - some values overlap between A and B and neither is solved.. force all');
          let v = domain_min(AB);
          let V = domain_createValue(v);
          setDomain(indexA, V);
          setDomain(indexB, V);
          R = domain_resolveAsBooly(R, true);
        }
        TRACE(' - R is now', domain__debug(R));
        ASSERT(R, 'leaf should at least have the resulting value');
        setDomain(indexR, R);
      } else if (domain_isZero(R)) {
        TRACE(' - R=0 so make sure AB is empty');
        if (AB) {
          TRACE(' - it wasnt, making it so now');
          if (domain_isSolved(A)) setDomain(indexB, domain_removeValue(B, domain_getValue(A)));
          else setDomain(indexA, domain_removeValue(A, force(indexB)));
        }
      } else {
        force(indexA, AB);
        force(indexB, getDomain(indexA));
      }

      ASSERT(getDomain(indexR));
      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexB));
      ASSERT(!domain_isBooly(getDomain(indexR)));
      ASSERT(domain_isSolved(getDomain(indexA)) || domain_isSolved(getDomain(indexB)) || !domain_intersection(getDomain(indexA), getDomain(indexB)), 'either A or B is solved OR they have no intersecting values');
      ASSERT(!!domain_intersection(getDomain(indexA), getDomain(indexB)) === !domain_isZero(getDomain(indexR)));
      ASSERT(!domain_isZero(getDomain(indexR)) ? domain_isSolved(getDomain(indexA)) && domain_isSolved(getDomain(indexB)) : true, 'if R>0 then A and B must be solved');
    });

    ml_eliminate(ml, offset, SIZEOF_CR_2);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    somethingChanged();
  }

  function leaf_issome(ml, offset, indexR, argCount) {
    TRACE('   - leaf_issome; index', indexR, 'is a leaf var, R = some?(A B ...), index=', indexR, ', R=', domain__debug(getDomain(indexR)));
    TRACE_MORPH('R = some(...)', '');

    let args = markAndCollectArgs(ml, offset, argCount);

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_issome');

      let has = false;
      for (let i = 0; i < args.length; ++i) {
        let index = args[i];
        if (force(index) > 0) {
          has = true;
          break;
        }
      }

      let R = getDomain(indexR);
      if (has) R = domain_removeValue(R, 0);
      else R = domain_removeGtUnsafe(R, 0);

      ASSERT(R, 'leaf should at least have the resulting value');
      setDomain(indexR, R);
    });

    ml_eliminate(ml, offset, SIZEOF_C + argCount * 2 + 2);
    bounty_markVar(bounty, indexR);
    somethingChanged();
  }

  function leaf_lt(ml, offset, indexA, indexB, leafSide) {
    TRACE('   - leaf_lt;', leafSide, 'is a leaf var, A < B,', indexA, '<', indexB);
    ASSERT(typeof indexA === 'number', 'index A should be number', indexA);
    ASSERT(typeof indexB === 'number', 'index B should be number', indexB);

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_lt; solving', indexA, '<', indexB, '  ->  ', domain__debug(getDomain(indexA)), '<', domain__debug(getDomain(indexB)));

      let A = getDomain(indexA);
      let B = getDomain(indexB);

      let maxA = domain_max(A);
      let minB = domain_min(B);

      // numdom([28,29]) < numdom([15,30])
      TRACE(' - maxA >=? minB;', maxA, '>=', minB);

      if (maxA < minB) {
        TRACE(' - lt already fulfilled, no change required');
      } else if (domain_min(A) >= minB) {
        let vA = domain_min(A);
        TRACE(' - min(A) still larger than min(B) so setting A to min(A)=', vA, ' and removing all LTE from B');
        TRACE(' - so;', domain__debug(A), '=>', domain__debug(domain_removeGtUnsafe(A, vA)), 'and', domain__debug(B), '=>', domain__debug(domain_removeLte(B, vA)));
        setDomain(indexA, domain_removeGtUnsafe(A, vA));
        setDomain(indexB, domain_removeLte(B, vA));
      } else {
        TRACE(' - removing >=min(B) from A');
        setDomain(indexA, domain_removeGte(A, minB));
      }
      TRACE(' - result:', domain__debug(getDomain(indexA)), '<=', domain__debug(getDomain(indexB)));

      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexB));
      ASSERT(domain_max(getDomain(indexA)) < domain_min(getDomain(indexB)));
    });

    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    somethingChanged();
  }

  function leaf_lte(ml, offset, indexA, indexB, leafIsA) {
    TRACE('   - leaf_lte;', leafIsA ? 'A' : 'B', 'is a leaf var, A <= B,', indexA, '<=', indexB);
    ASSERT(typeof indexA === 'number', 'index A should be number', indexA);
    ASSERT(typeof indexB === 'number', 'index B should be number', indexB);

    // prune values that cant be a solution
    let A = getDomain(indexA, true);
    let B = getDomain(indexB, true);
    let minA = domain_min(A);
    let maxB = domain_max(B);
    let nA = domain_removeGtUnsafe(A, maxB);
    let nB = domain_removeLtUnsafe(B, minA);
    if (!nA || domain_isSolved(nA) || !nB || domain_isSolved(nB)) {
      TRACE(' - lte can be solved by minimizer');
      TRACE(' - either solved after pruning?', domain__debug(nA), domain__debug(nB));
      TRACE(nA ? '' : ' - A without max(B) is empty; A=', domain__debug(A), ', B=', domain__debug(B), ', max(B)=', domain_max(B), ', result:', domain_removeGtUnsafe(A, maxB));
      requestAnotherCycle = true;
      return false;
    }
    if (A !== nA) setDomain(indexA, nA);
    if (B !== nB) setDomain(indexB, nB);

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_lte; solving', indexA, '<=', indexB, '  ->  ', domain__debug(getDomain(indexA)), '<=', domain__debug(getDomain(indexB)), '  ->  ', domain_max(getDomain(indexA)), '<=', domain_min(getDomain(indexB)));

      let A = getDomain(indexA);
      let B = getDomain(indexB);
      let maxA = domain_max(A);
      let minB = domain_min(B);

      TRACE(' - maxA >? minB;', maxA, '>', minB);
      if (maxA > minB) {
        if (leafIsA) {
          let nA = domain_removeGtUnsafe(A, minB);
          TRACE('   - trimmed A down to', domain__debug(nA));
          setDomain(indexA, nA);
        } else {
          let nB = domain_removeLtUnsafe(B, maxA);
          TRACE('   - trimmed B down to', domain__debug(nB));
          setDomain(indexB, nB);
        }
      }

      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexB));
      ASSERT(domain_max(getDomain(indexA)) <= domain_min(getDomain(indexB)));
    });

    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    somethingChanged();
    return true;
  }

  function leaf_some_2(ml, offset, leafIndex, otherIndex, indexA, indexB) {
    TRACE('   - leaf_some_2;', leafIndex, 'is a leaf var, A | B,', indexA, '|', indexB);

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_some_2');
      let A = getDomain(otherIndex);
      let B = getDomain(leafIndex);
      TRACE(' - solving', indexA, '|', indexB, '  ->  ', domain__debug(A), '|', domain__debug(B));

      // check if either is solved to zero, in that case force the other to non-zero.
      // if neither is zero and both have zero, force the leaf to non-zero.
      // otherwise no change because OR will be satisfied.

      if (domain_isZero(A)) {
        TRACE(' - forcing the leaf index,', leafIndex, ', to non-zero because the other var is zero');
        setDomain(leafIndex, domain_removeValue(B, 0));
      } else if (domain_isZero(B)) {
        TRACE(' - forcing the other index,', otherIndex, ', to non-zero because the leaf var was already zero');
        setDomain(otherIndex, domain_removeValue(A, 0));
      } else if (!domain_hasNoZero(A) && !domain_hasNoZero(A)) {
        TRACE(' - neither was booly solved so forcing the leaf index,', leafIndex, ', to non-zero to satisfy the OR');
        setDomain(leafIndex, domain_removeValue(B, 0));
      } else {
        TRACE(' - no change.');
      }
    });

    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, leafIndex);
    bounty_markVar(bounty, otherIndex);
    somethingChanged();
  }

  function leaf_sum_result(ml, offset, argCount, indexR) {
    TRACE('   - leaf_sum_result;', indexR, 'is a leaf var, R = sum(', argCount, 'x ),', indexR, '= sum(...)');

    let args = markAndCollectArgs(ml, offset, argCount);

    TRACE('   - collected sum arg indexes;', args);
    TRACE('   - collected sum arg domains;', args.map(index => domain__debug(getDomain(index))).join(', '));

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_sum_result');
      TRACE(' -', indexR, '= sum(', args, ')');
      TRACE(' -', domain__debug(getDomain(indexR)), '= sum(', args.map(index => domain__debug(getDomain(index))).join(', '), ')');

      let sum = 0;
      for (let i = 0; i < args.length; ++i) {
        let index = args[i];
        let v = force(index);
        sum += v;
        TRACE(' - i=', i, ', index=', index, ', v=', v, ', sum now:', sum);
      }

      TRACE(' - total sum is', sum);
      let R = domain_intersectionValue(getDomain(indexR), sum);
      ASSERT(R, 'R should contain solution value');
      setDomain(indexR, R);
    });

    ml_eliminate(ml, offset, SIZEOF_C + argCount * 2 + 2);
    bounty_markVar(bounty, indexR); // args already done in above loop
    somethingChanged();
  }

  function leaf_xnor(ml, offset, leafIndex, otherIndex, indexA, indexB) {
    TRACE('   - leaf_xnor;', leafIndex, 'is a leaf var, A !^ B,', indexA, '!^', indexB);
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'should have 2 args');

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_xnor; solving', indexA, '!^', indexB, '  ->  ', domain__debug(getDomain(indexA)), '!^', domain__debug(getDomain(indexB)));

      // check if a var is solved to zero, if so solve the other var to zero as well
      // check if a var is solved to non-zero, if so solve the other var to non-zero as well
      // otherwise force(A), let B follow that result

      let A = getDomain(indexA);
      let B = getDomain(indexB);
      if (domain_isZero(A)) {
        TRACE(' - forcing B to zero because A is zero');
        setDomain(indexB, domain_removeGtUnsafe(B, 0));
      } else if (domain_isZero(B)) {
        TRACE(' - forcing A to zero because B is zero');
        setDomain(indexA, domain_removeGtUnsafe(A, 0));
      } else if (domain_hasNoZero(A)) {
        TRACE(' - forcing B to non-zero because A is non-zero');
        setDomain(indexB, domain_removeValue(B, 0));
      } else if (domain_hasNoZero(B)) {
        TRACE(' - forcing A to non-zero because B is non-zero');
        setDomain(indexA, domain_removeValue(A, 0));
      } else {
        // TODO: force() and repeat above steps
        TRACE(' - neither was booly solved. forcing both to non-zero', domain__debug(domain_removeValue(A, 0)), domain__debug(domain_removeValue(B, 0))); // non-zero gives more options? *shrug*
        setDomain(indexA, domain_removeValue(A, 0));
        setDomain(indexB, domain_removeValue(B, 0));
      }
    });

    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, leafIndex);
    bounty_markVar(bounty, otherIndex);
    somethingChanged();
  }

  function leaf_xor(ml, offset, leafIndex, otherIndex, indexA, indexB) {
    TRACE('   - leaf_xor;', leafIndex, 'is a leaf var, A ^ B,', indexA, '^', indexB);

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - leaf_xor; solving', indexA, '^', indexB, '  ->  ', domain__debug(getDomain(indexA)), '^', domain__debug(getDomain(indexB)));

      // check if either is solved to zero, in that case force the other to non-zero.
      // check if either side is non-zero. in that case force the other to zero
      // confirm that both sides are booly-solved, force them to if not.

      let A = getDomain(indexA);
      let B = getDomain(indexB);
      if (domain_isZero(A)) {
        TRACE(' - forcing B to non-zero because A is zero');
        setDomain(indexB, domain_removeValue(B, 0));
      } else if (domain_isZero(B)) {
        TRACE(' - forcing A to non-zero because B was already zero');
        setDomain(indexA, domain_removeValue(A, 0));
      } else if (domain_hasNoZero(A)) {
        TRACE(' - A was non-zero so forcing B to zero');
        setDomain(indexB, domain_removeGtUnsafe(B, 0));
      } else if (domain_hasNoZero(B)) {
        TRACE(' - B was non-zero so forcing A to zero');
        setDomain(indexA, domain_removeGtUnsafe(A, 0));
      } else {
        TRACE(' - neither was booly solved. forcing A to zero and B to non-zero');
        setDomain(indexA, domain_removeValue(A, 0));
        setDomain(indexB, domain_removeGtUnsafe(B, 0));
      }
    });

    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, leafIndex);
    bounty_markVar(bounty, otherIndex);
    somethingChanged();
  }

  // ##############

  function desubset_diff(ml, diffOffset, diffArgCount, diffFirstIndex, diffFirstIndexCounts) {
    TRACE(' - desubset_diff; checking whether given DIFF at', diffOffset, 'is entirely a smaller subset than another DIFF');
    TRACE('   - argCount=', diffArgCount, ', indexA=', diffFirstIndex, ', diffFirstIndexCounts=', diffFirstIndexCounts);

    // a diff can superset another diff
    // a diff can superset-or-equal an isdiff and R=1 the isdiff
    // a diff can subset-or-equal an issame and R=0 the issame

    // both DIFFs must be ordered for this to work. but try to postpone sorting as much as possible (=expensive)
    let sortedGivenDiff = false;

    for (let i = 0; i < diffFirstIndexCounts; ++i) {
      let offset = bounty_getOffset(bounty, diffFirstIndex, i);
      if (offset !== diffOffset) {
        let opCode = ml_dec8(ml, offset);
        if (opCode === ML_DIFF) {
          // diff(ABC) ⊂ diff(ABCD)  then the bigger set can be removed
          let argCount = ml_dec16(ml, offset + 1);
          if (diffArgCount > argCount) { // only check if given DIFF has more args than current DIFF. always.
            // first ensure both DIFF op args are ordered
            if (!sortedGivenDiff) dealiasAndSortArgs(ml, diffOffset, diffArgCount);
            dealiasAndSortArgs(ml, offset, argCount);
            if (isSubset(ml, offset, argCount, diffOffset, diffArgCount)) { // note: inverted args!
              TRACE(' - deduped a DIFF subset of another DIFF! marking all args and eliminating the larger DIFF');
              markAllArgs(ml, offset, argCount); // note: this also marks all args of DIFF1 ;)
              ml_eliminate(ml, offset, SIZEOF_C + argCount * 2);
              return true;
            }
            TRACE(' - this diff was not a subset of the other diff');
          }
        } else if (opCode === ML_ISDIFF) {
          // diff(ABC) ⊆ R=diff?(ABCD)  then R=1 and isdiff dropped because the DIFF() will ensure it
          let argCount = ml_dec16(ml, offset + 1);
          if (diffArgCount >= argCount) { // only check if DIFF has >= args than ISDIFF
            // first ensure both DIFF op args are ordered
            if (!sortedGivenDiff) dealiasAndSortArgs(ml, diffOffset, diffArgCount);
            dealiasAndSortArgs(ml, offset, argCount);
            if (isSubset(ml, offset, argCount, diffOffset, diffArgCount)) { // note: inverted args!
              TRACE(' - deduped a DIFF subset of an ISDIFF! Setting R=1, marking all args, and eliminating the ISDIFF');
              let indexR = readIndex(ml, offset + SIZEOF_C + argCount * 2);
              TRACE(' - indexR=', indexR);
              let R = getDomain(indexR);
              let nR = domain_removeValue(R, 0);
              if (R !== nR) setDomain(indexR, nR);
              markAllArgs(ml, offset, argCount); // note: this also marks all args of DIFF1 ;)
              ml_eliminate(ml, offset, SIZEOF_C + argCount * 2 + 2);
              return true;
            }
            TRACE(' - this DIFF was not a subset of the ISDIFF');
          }
        } else if (opCode === ML_ISSAME) {
          // DIFF(ABC) ⊆ R=SAME?(ABCD)  then R=0 and ISSAME dropped because the DIFF() _will_ negate it
          let argCount = ml_dec16(ml, offset + 1);
          if (diffArgCount <= argCount) { // only check if DIFF has fewer or equal args than ISSAME
            // first ensure both DIFF op args are ordered
            if (!sortedGivenDiff) dealiasAndSortArgs(ml, diffOffset, diffArgCount);
            dealiasAndSortArgs(ml, offset, argCount);
            if (isSubset(ml, diffOffset, diffArgCount, offset, argCount)) {
              TRACE(' - deduped a DIFF subset of an ISSAME! Setting R=0, marking all args, and eliminating the ISSAME');
              let indexR = readIndex(ml, offset + SIZEOF_C + argCount * 2);
              TRACE(' - indexR=', indexR);
              let R = getDomain(indexR);
              let nR = domain_removeGtUnsafe(R, 0);
              if (R !== nR) setDomain(indexR, nR);
              markAllArgs(ml, offset, argCount); // note: this also marks all args of DIFF1 ;)
              ml_eliminate(ml, offset, SIZEOF_C + argCount * 2 + 2);
              return true;
            }
            TRACE(' - this DIFF was not a subset of the ISSAME');
          }
        }
      }
    }
    TRACE(' / desubset_diff');
  }

  function desubset_nall(ml, nallOffset, nallArgCount, nallFirstIndex, nallFirstIndexCounts) {
    TRACE(' - desubset_nall; checking whether given NALL at', nallOffset, 'is entirely a smaller subset than another NALL');
    TRACE('   - argCount=', nallArgCount, ', indexA=', nallFirstIndex, ', nallFirstIndexCounts=', nallFirstIndexCounts);

    // a nall can subset another nall
    // a nall can subset-or-equal an isnall and R=1 the isnall
    // a nall can subset-or-equal an isall and R=0 the isnall

    // both NALLs must be ordered for this to work. but try to postpone sorting as much as possible (=expensive)
    let sortedGivenNall = false;

    for (let i = 0; i < nallFirstIndexCounts; ++i) {
      let offset = bounty_getOffset(bounty, nallFirstIndex, i);
      if (offset !== nallOffset) {
        let opCode = ml_dec8(ml, offset);
        if (opCode === ML_NALL) {
          // nall(ABC) ⊂ nall(ABCD)  then the bigger set can be removed
          let argCount = ml_dec16(ml, offset + 1);
          if (nallArgCount < argCount) { // only check if given NALL has fewer args than current NALL. always.
            // first ensure both NALL op args are ordered
            if (!sortedGivenNall) dealiasAndSortArgs(ml, nallOffset, nallArgCount);
            dealiasAndSortArgs(ml, offset, argCount);
            if (isSubset(ml, nallOffset, nallArgCount, offset, argCount)) {
              TRACE(' - deduped a NALL subset of another NALL! marking all args and eliminating the larger NALL');
              markAllArgs(ml, offset, argCount); // note: this also marks all args of NALL1 ;)
              ml_eliminate(ml, offset, SIZEOF_C + argCount * 2);
              return true;
            }
            TRACE(' - this nall was not a subset of the other nall');
          }
        } else if (opCode === ML_ISNALL) {
          // nall(ABC) ⊆ R=nall?(ABCD)  then R=1 and isnall dropped because the NALL() will ensure it
          let argCount = ml_dec16(ml, offset + 1);
          if (nallArgCount <= argCount) { // only check if NALL has fewer or equal args than ISNALL
            // first ensure both NALL op args are ordered
            if (!sortedGivenNall) dealiasAndSortArgs(ml, nallOffset, nallArgCount);
            dealiasAndSortArgs(ml, offset, argCount);
            if (isSubset(ml, nallOffset, nallArgCount, offset, argCount)) {
              TRACE(' - deduped a NALL subset of an ISNALL! Setting R=1, marking all args, and eliminating the ISNALL');
              let indexR = readIndex(ml, offset + SIZEOF_C + argCount * 2);
              TRACE(' - indexR=', indexR);
              let R = getDomain(indexR);
              let nR = domain_removeValue(R, 0);
              if (R !== nR) setDomain(indexR, nR);
              markAllArgs(ml, offset, argCount); // note: this also marks all args of NALL1 ;)
              ml_eliminate(ml, offset, SIZEOF_C + argCount * 2 + 2);
              return true;
            }
            TRACE(' - this NALL was not a subset of the ISNALL');
          }
        } else if (opCode === ML_ISALL) {
          // NALL(ABC) ⊆ R=ALL?(ABCD)  then R=0 and ISALL dropped because the NALL() _will_ negate it
          let argCount = ml_dec16(ml, offset + 1);
          if (nallArgCount <= argCount) { // only check if NALL has fewer or equal args than ISALL
            // first ensure both NALL op args are ordered
            if (!sortedGivenNall) dealiasAndSortArgs(ml, nallOffset, nallArgCount);
            dealiasAndSortArgs(ml, offset, argCount);
            if (isSubset(ml, nallOffset, nallArgCount, offset, argCount)) {
              TRACE(' - deduped a NALL subset of an ISALL! Setting R=0, marking all args, and eliminating the ISALL');
              let indexR = readIndex(ml, offset + SIZEOF_C + argCount * 2);
              TRACE(' - indexR=', indexR);
              let R = getDomain(indexR);
              let nR = domain_removeGtUnsafe(R, 0);
              if (R !== nR) setDomain(indexR, nR);
              markAllArgs(ml, offset, argCount); // note: this also marks all args of NALL1 ;)
              ml_eliminate(ml, offset, SIZEOF_C + argCount * 2 + 2);
              return true;
            }
            TRACE(' - this NALL was not a subset of the ISALL');
          }
        }
      }
    }
  }

  function desubset_some(ml, someOffset, someArgCount, someFirstIndex, someFirstIndexCounts) {
    TRACE(' - desubset_some; checking whether given SOME at', someOffset, 'is entirely a smaller subset than another SOME');
    TRACE('   - argCount=', someArgCount, ', indexA=', someFirstIndex, ', someFirstIndexCounts=', someFirstIndexCounts);

    // a some can subset another some
    // a some can subset-or-equal an issome and R=1 the issome
    // a some can subset-or-equal an isnone and R=0 the isnone

    // both SAME's must be ordered for this to work. but try to postpone sorting as much as possible (=expensive)
    let sortedGivenSome = false;

    for (let i = 0; i < someFirstIndexCounts; ++i) {
      let offset = bounty_getOffset(bounty, someFirstIndex, i);
      if (offset !== someOffset) {
        let opCode = ml_dec8(ml, offset);
        if (opCode === ML_SOME) {
          // some(ABC) ⊂ some(ABCD)  then the bigger set can be removed
          let argCount = ml_dec16(ml, offset + 1);
          if (someArgCount < argCount) { // only check if given SOME has fewer args than current SOME. always.
            // first ensure both SOME op args are ordered
            if (!sortedGivenSome) dealiasAndSortArgs(ml, someOffset, someArgCount);
            dealiasAndSortArgs(ml, offset, argCount);
            if (isSubset(ml, someOffset, someArgCount, offset, argCount)) {
              TRACE(' - deduped a SOME subset of another SOME! marking all args and eliminating the larger SOME');
              markAllArgs(ml, offset, argCount); // note: this also marks all args of SOME1 ;)
              ml_eliminate(ml, offset, SIZEOF_C + argCount * 2);
              somethingChanged();
              return true;
            }
            TRACE(' - this SOME was not a subset of the other SOME');
          }
        } else if (opCode === ML_ISSOME) {
          // some(ABC) ⊆ R=some?(ABCD)  then R=1 and issome dropped because the SOME() will ensure it
          let argCount = ml_dec16(ml, offset + 1);
          if (someArgCount <= argCount) { // only check if SOME has fewer or equal args than ISSOME
            // first ensure both SOME op args are ordered
            if (!sortedGivenSome) dealiasAndSortArgs(ml, someOffset, someArgCount);
            dealiasAndSortArgs(ml, offset, argCount);
            if (isSubset(ml, someOffset, someArgCount, offset, argCount)) {
              TRACE(' - deduped a SOME subset of an ISSOME! Setting R=1, marking all args, and eliminating the ISSOME');
              let indexR = readIndex(ml, offset + SIZEOF_C + argCount * 2);
              TRACE(' - indexR=', indexR);
              let R = getDomain(indexR);
              let nR = domain_removeValue(R, 0);
              if (R !== nR) setDomain(indexR, nR);
              markAllArgs(ml, offset, argCount); // note: this also marks all args of SOME1 ;)
              ml_eliminate(ml, offset, SIZEOF_C + argCount * 2 + 2);
              somethingChanged();
              return true;
            }
            TRACE(' - this some was not a subset of the issome');
          }
        } else if (opCode === ML_ISNONE) {
          // SOME(ABC) ⊆ R=NONE?(ABCD)  then R=0 and ISNONE dropped because the SOME() _will_ negate it
          let argCount = ml_dec16(ml, offset + 1);
          if (someArgCount <= argCount) { // only check if SOME has fewer or equal args than ISNONE
            // first ensure both SOME op args are ordered
            if (!sortedGivenSome) dealiasAndSortArgs(ml, someOffset, someArgCount);
            dealiasAndSortArgs(ml, offset, argCount);
            if (isSubset(ml, someOffset, someArgCount, offset, argCount)) {
              TRACE(' - deduped a SOME subset of an ISNONE! Setting R=0, marking all args, and eliminating the ISNONE');
              let indexR = readIndex(ml, offset + SIZEOF_C + argCount * 2);
              TRACE(' - indexR=', indexR);
              let R = getDomain(indexR);
              let nR = domain_removeGtUnsafe(R, 0);
              if (R !== nR) setDomain(indexR, nR);
              markAllArgs(ml, offset, argCount); // note: this also marks all args of SOME1 ;)
              ml_eliminate(ml, offset, SIZEOF_C + argCount * 2 + 2);
              somethingChanged();
              return true;
            }
            TRACE(' - this SOME was not a subset of the ISNONE');
          }
        }
      }
    }
  }

  function isSubset(ml, someOffset1, argCount1, someOffset2, argCount2) {
    // now "zip" and confirm that all args in SOME1 are present by SOME2.
    let pos1 = 0;
    let pos2 = 0;
    let index1 = ml_dec16(ml, someOffset1 + SIZEOF_C + pos1 * 2);
    let index2 = 0;
    while (pos2 < argCount2) {
      index2 = ml_dec16(ml, someOffset2 + SIZEOF_C + pos2 * 2);
      while (index1 === index2) {
        ++pos1;
        if (pos1 >= argCount1) {
          return true;
        }
        index1 = ml_dec16(ml, someOffset1 + SIZEOF_C + pos1 * 2);
      }
      ++pos2;
    }
    return false;
  }
  function dealiasAndSortArgs(ml, offset, argCount) {
    TRACE(' - dealiasAndSortArgs; sorting and dealiasing', argCount, 'args starting at', offset);

    // first de-alias all args
    for (let i = 0; i < argCount; ++i) {
      let argOffset = offset + SIZEOF_C + i * 2;
      let actual = ml_dec16(ml, argOffset);
      let alias = getAlias(actual);
      if (actual !== alias) ml_enc16(ml, argOffset, alias);
    }
    // now sort them
    ml_heapSort16bitInline(ml, offset + SIZEOF_C, argCount);
  }

  // ##############

  function trick_sum_to_nall(ml, offset, argCount, indexR) {
    // [0 0 n-1 n-1]=sum([01] [01] [01]   =>   nall(...)
    TRACE('   - trick_sum_to_nall');
    TRACE_MORPH('[0 0 n-1 n-1]=sum(A:[01] B:[01] C:[01] ...)', 'nall(A B C ...)');
    TRACE('   - indexR:', indexR, ', R:', domain__debug(getDomain(indexR)));
    TRACE('   -', ml__debug(ml, offset, 1, problem));
    ASSERT(getDomain(indexR) === domain_createRange(0, argCount - 1) && domain_min(getDomain(indexR)) === 0 && domain_max(getDomain(indexR)) === argCount - 1);

    let args = markAndCollectArgs(ml, offset, argCount);
    TRACE('   - args:', args, ', doms:', args.map(getDomain).map(domain__debug).join(', '));
    ASSERT(args.map(getDomain).every(domain_isBool), 'all args should be bool');

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - trick_sum_to_nall');
      TRACE(' -', indexR, '= sum(', args, ')');
      TRACE(' -', domain__debug(getDomain(indexR)), '= sum(', args.map(index => domain__debug(getDomain(index))), ')');

      let R = getDomain(indexR);

      TRACE(' - scan first');
      let current = 0;
      for (let i = 0; i < args.length; ++i) {
        let index = args[i];
        let D = getDomain(index);
        let vD = domain_getValue(D);
        if (vD >= 0) current += vD;
      }

      let vR = domain_min(domain_removeLtUnsafe(R, current)); // "R must be at least the current sum of constant args"
      let remaining = vR - current;
      TRACE(' - args that are solved currently sum to', current, ', R=', domain__debug(R), ', so there is', remaining, 'to be added');

      for (let i = 0; i < args.length; ++i) {
        let index = args[i];
        let D = getDomain(index);
        if (!domain_isSolved(D)) {
          if (remaining > 0) {
            D = domain_removeValue(D, 0);
            --remaining;
          } else {
            D = domain_removeValue(D, 1);
          }
          // SUM requires all args to solve. let them pick any value from what remains.
          force(index, D);
        }
      }

      setDomain(indexR, domain_intersectionValue(R, vR));

      ASSERT(getDomain(indexR));
      ASSERT(domain_isSolved(getDomain(indexR)));
      ASSERT(domain_getValue(getDomain(indexR)) === args.reduce((a, b) => a + force(b), 0));
    });

    // from sum to nall.
    ml_cr2c(ml, offset, argCount, ML_NALL, args);
    bounty_markVar(bounty, indexR); // args already done in above loop
    somethingChanged();
  }

  function trick_some_sum(ml, offset, argCount, indexR) {
    // [1 1 n n]=sum([01] [01] [01]   ->   nall(...)
    TRACE('   - trick_some_sum; [1 1 n n]=sum([01] [01] [01] ...) is actually a SOME', indexR);

    let args = markAndCollectArgs(ml, offset, argCount);

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - trick_some_sum');
      TRACE(' - some(A B);', indexR, '= sum(', args, ')  ->  ', domain__debug(getDomain(indexR)), '= sum(', args.map(index => domain__debug(getDomain(index))), ')');

      // first make sure at least one arg is nonzero. for once if none already is.
      let none = true;
      let booly = -1;
      for (let i = 0; i < argCount; ++i) {
        let index = args[i];
        let D = getDomain(index);
        if (domain_hasNoZero(D)) {
          none = false;
          break;
        }
        if (!domain_isZero(D)) {
          ASSERT(domain_isBooly(D));
          booly = index;
        }
      }
      if (none) {
        ASSERT(booly >= 0);
        let D = getDomain(booly);
        D = domain_removeValue(D, 0);
        setDomain(booly, D);
        ASSERT(D);
      }
      // now collect the sum. do it in a new loop because it's just simpler that way.
      // force all the args because otherwise the sum might be violated
      let sum = 0;
      for (let i = 0; i < argCount; ++i) {
        sum += force(args[i]);
      }
      // set R to the sum of all constants
      let R = getDomain(indexR);
      R = domain_intersectionValue(R, sum);
      setDomain(indexR, R);
      ASSERT(R);
    });

    // from sum to some.
    ml_enc8(ml, offset, ML_SOME);
    ml_enc16(ml, offset + 1, argCount);
    for (let i = 0; i < argCount; ++i) {
      ml_enc16(ml, offset + SIZEOF_C + i * 2, args[i]);
    }
    ml_compileJumpSafe(ml, offset + SIZEOF_C + argCount * 2, 2); // result var (16bit). for the rest some is same as sum
    bounty_markVar(bounty, indexR); // args already done in above loop
    somethingChanged();
  }

  function trick_isall_ltelhs_1shared(ml, lteOffset, indexR, countsR) {
    let indexS = readIndex(ml, lteOffset + OFFSET_C_B);

    TRACE('trick_isall_ltelhs_1shared');
    TRACE(' - with only R shared on an isall[2]:');
    TRACE('   - R <= S, R = all?(A B)      =>      some(S | nall?(A B))');
    TRACE(' - indexes:', indexR, '<=', indexS);
    TRACE(' - domains:', getDomain(indexR), '<=', getDomain(indexS));
    TRACE(' - metaFlags:', bounty__debugMeta(bounty, indexR), '<=', bounty__debugMeta(bounty, indexS));

    // the next asserts should have been verified by the bounty hunter, so they are only verified in ASSERTs
    ASSERT(countsR === 2, 'R should be a leaf var with these two constraints');
    ASSERT(countsR === getCounts(bounty, indexR), 'correct value?');
    ASSERT(getMeta(bounty, indexR) === (BOUNTY_FLAG_LTE_LHS | BOUNTY_FLAG_ISALL_RESULT), 'A be an lte lhs and isall result var');
    ASSERT(ml_dec8(ml, lteOffset) === ML_LTE, 'lteOffset should be lte');
    ASSERT(ml_dec16(ml, lteOffset + OFFSET_C_A) === indexR, 'shared index should be lhs of lteOffset');

    if (!domain_isBool(getDomain(indexR, true)) || !domain_isBool(getDomain(indexS, true))) {
      TRACE(' - R or S wasnt bool, bailing');
      return false;
    }

    let offset1 = bounty_getOffset(bounty, indexR, 0);
    let offset2 = bounty_getOffset(bounty, indexR, 1);
    let isallOffset = offset1 === lteOffset ? offset2 : offset1;

    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL);
    ASSERT(readIndex(ml, isallOffset + OFFSET_C_R) === indexR);

    if (ml_dec16(ml, isallOffset + 1) !== 2) {
      TRACE(' - isall did not have 2 args, bailing');
      return false;
    }

    let indexA = readIndex(ml, isallOffset + OFFSET_C_A);
    let indexB = readIndex(ml, isallOffset + OFFSET_C_B);

    if (!domain_isBool(getDomain(indexA, true)) || !domain_isBool(getDomain(indexB, true))) {
      TRACE(' - A or B wasnt bool, bailing');
      return false;
    }

    TRACE_MORPH('R <= S, R = all?(A B)', 'S | nall?(A B)');

    TRACE(' - change the isall to an isnall, change the LTE to an OR');

    ml_cr2cr2(ml, isallOffset, 2, ML_ISNALL, indexA, indexB, indexR);
    ml_c2c2(ml, lteOffset, 2, ML_SOME, indexR, indexS);

    bounty_markVar(bounty, indexR);
    bounty_markVar(bounty, indexS);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    somethingChanged();
    return true;
  }

  function trick_isall_implhs_1shared(ml, impOffset, indexR, countsR) {
    let indexS = readIndex(ml, impOffset + OFFSET_C_B);

    TRACE('trick_isall_implhs_1shared');
    TRACE(' - with only R shared on an isall[2]:');
    TRACE('   - R -> S, R = all?(A B)      =>      some(S | nall?(A B))');
    TRACE(' - indexes:', indexR, '<=', indexS);
    TRACE(' - domains:', getDomain(indexR), '<=', getDomain(indexS));
    TRACE(' - metaFlags:', bounty__debugMeta(bounty, indexR), '<=', bounty__debugMeta(bounty, indexR));

    // the next asserts should have been verified by the bounty hunter, so they are only verified in ASSERTs
    ASSERT(countsR === 2, 'R should be a leaf var with these two constraints');
    ASSERT(countsR === getCounts(bounty, indexR), 'correct value?');
    ASSERT(getMeta(bounty, indexR) === (BOUNTY_FLAG_IMP_LHS | BOUNTY_FLAG_ISALL_RESULT), 'A be an imp lhs and isall result var');
    ASSERT(ml_dec8(ml, impOffset) === ML_IMP, 'impOffset should be imp');
    ASSERT(ml_dec16(ml, impOffset + OFFSET_C_A) === indexR, 'shared index should be lhs of impOffset');

    if (!domain_isBool(getDomain(indexR, true)) || !domain_isBool(getDomain(indexS, true))) {
      TRACE(' - R or S wasnt bool, bailing');
      return false;
    }

    let offset1 = bounty_getOffset(bounty, indexR, 0);
    let offset2 = bounty_getOffset(bounty, indexR, 1);
    let isallOffset = offset1 === impOffset ? offset2 : offset1;

    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL);
    ASSERT(readIndex(ml, isallOffset + OFFSET_C_R) === indexR);

    if (ml_dec16(ml, isallOffset + 1) !== 2) {
      TRACE(' - isall did not have 2 args, bailing');
      return false;
    }

    if (!domain_isBool(getDomain(indexA, true)) || !domain_isBool(getDomain(indexB, true))) {
      TRACE(' - A or B wasnt bool, bailing');
      return false;
    }

    TRACE_MORPH('R -> S, R = all?(A B)', 'S | nall?(A B)');

    TRACE(' - change the isall to a nall, change the imp to an or');

    let indexA = readIndex(ml, isallOffset + OFFSET_C_A);
    let indexB = readIndex(ml, isallOffset + OFFSET_C_B);

    ml_cr2cr2(ml, isallOffset, 2, ML_ISNALL, indexA, indexB, indexR);
    ml_c2c2(ml, impOffset, 2, ML_SOME, indexR, indexS);

    bounty_markVar(bounty, indexR);
    bounty_markVar(bounty, indexS);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    somethingChanged();
    return true;
  }

  function trick_isall_ltelhs_2shared(ml, lteOffset, indexR, countsR) {
    let indexA = readIndex(ml, lteOffset + OFFSET_C_B);

    TRACE('trick_isall_ltelhs_2shared');
    TRACE(' - with R and an arg shared:');
    TRACE('   - R <= A, R = all?(A B ...)      ->      R = all?(A B ...)');
    TRACE('   - (the isall subsumes the lte, regardless of other constraints)');
    //TRACE(' - with only R shared:');
    //TRACE('   - R <= A, R = all?(B C)          ->      some(C nall?(A B))');
    //TRACE('   - (when R is leaf, only A=1 B=1 C=0 is false)');
    TRACE(' - indexes:', indexR, '<=', indexA);
    TRACE(' - domains:', getDomain(indexR), '<=', getDomain(indexA));
    TRACE(' - metaFlags:', bounty__debugMeta(bounty, indexR), '<=', bounty__debugMeta(bounty, indexR));

    // the next asserts should have been verified by the bounty hunter, so they are only verified in ASSERTs
    ASSERT(countsR > 1, 'the indexR should be part of at least two constraints');
    ASSERT(countsR === getCounts(bounty, indexR), 'correct value?');
    ASSERT(hasFlags(getMeta(bounty, indexR), BOUNTY_FLAG_LTE_LHS | BOUNTY_FLAG_ISALL_RESULT), 'A must at least be an lte lhs and isall result var');
    ASSERT(ml_dec8(ml, lteOffset) === ML_LTE, 'lteOffset should be lte');
    ASSERT(ml_dec16(ml, lteOffset + OFFSET_C_A) === indexR, 'shared index should be lhs of lteOffset');

    let toCheck = Math.min(countsR, BOUNTY_MAX_OFFSETS_TO_TRACK);

    // note: it's not guaranteed that we'll actually see an isall in this loop
    // if countsR is higher than the max number of offsets tracked by bounty
    // in that case nothing happens and the redundant constraint persists. no biggie
    for (let i = 0; i < toCheck; ++i) {
      TRACE('   - fetching #', i, '/', toCheck, '(', countsR, '||', BOUNTY_MAX_OFFSETS_TO_TRACK, ')');
      let offset = bounty_getOffset(bounty, indexR, i);
      TRACE('   - #' + i, ', offset =', offset);
      if (offset !== lteOffset) {
        let op = ml_dec8(ml, offset);
        if (op === ML_ISALL) {
          if (_trick_isall_ltelhs_2shared(lteOffset, offset, indexR, indexA)) return true;
        }
      }
    }

    TRACE(' - trick_isall_ltelhs_2shared changed nothing');
    return false;
  }
  function _trick_isall_ltelhs_2shared(lteOffset, isallOffset, indexR, indexA) {
    // R <= A, R = all?(A B C ...)    =>     R = all?(A B C ...)   (drop lte)
    // need to search the isall for the A arg here
    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'should be isall');

    let argCount = ml_dec16(ml, isallOffset + 1);
    let indexS = readIndex(ml, isallOffset + SIZEOF_C + argCount * 2);
    TRACE('     - isall with an argCount of', argCount, ', indexR=', indexS, '=indexR=', indexR, 'cross checking all args to match', indexA);
    ASSERT(indexS === indexR, 'R should (at least) be result of isall');

    // scan for any arg index == A
    for (let i = 0; i < argCount; ++i) {
      let argIndex = readIndex(ml, isallOffset + SIZEOF_C + i * 2);
      if (argIndex === indexA) {
        TRACE_MORPH('R <= A, R = all?(A ...)', 'R = all?(A ...)', 'The isall subsumes the lte');
        TRACE('     - arg index is indexA, match. this is R <= A, R = all?(A ...) so eliminate the lte');
        ml_eliminate(ml, lteOffset, SIZEOF_C_2);
        bounty_markVar(bounty, indexR);
        bounty_markVar(bounty, indexA);
        somethingChanged();
        return true;
      }
    }
    return false;
  }

  function trick_implhs_isall_2shared(ml, impOffset, indexA, countsA) {
    TRACE('trick_implhs_isall_2shared', indexA, 'at', impOffset, 'metaFlags:', bounty__debugMeta(bounty, indexA), '`S -> A, S = all?(A B ...)   ->   S = all?(A B ...)`');
    TRACE(' - imp:', indexA, '->', readIndex(ml, impOffset + OFFSET_C_B), '  =>  ', domain__debug(getDomain(indexA, true)), '->', domain__debug(getDomain(readIndex(ml, impOffset + OFFSET_C_B), true)));
    TRACE('   - S -> A, S = all?(A B)   =>   S = all?(A B)');
    TRACE('   - (the isall subsumes the implication, regardless of other constraints)');

    // the next asserts should have been verified by the bounty hunter, so they are only verified in ASSERTs
    ASSERT(countsA > 1, 'the indexA should only be part of two constraints', countsA, bounty__debugMeta(bounty, indexA));
    ASSERT(countsA === getCounts(bounty, indexA), 'correct value?', countsA === getCounts(bounty, indexA));
    ASSERT(hasFlags(getMeta(bounty, indexA), BOUNTY_FLAG_IMP_LHS | BOUNTY_FLAG_ISALL_RESULT), 'A must at least be an imp lhs and isall result var');
    ASSERT(ml_dec8(ml, impOffset) === ML_IMP, 'impOffset should be imp', ml__opName(ml_dec8(ml, impOffset)));
    ASSERT(ml_dec16(ml, impOffset + OFFSET_C_A) === indexA, 'shared index should be lhs of impOffset');

    let indexB = readIndex(ml, impOffset + OFFSET_C_B);

    let toCheck = Math.min(countsA, BOUNTY_MAX_OFFSETS_TO_TRACK);

    // note: it's not guaranteed that we'll actually see an isall in this loop
    // if countsA is higher than the max number of offsets tracked by bounty
    // in that case nothing happens and the redundant constraint persists. no biggie
    for (let i = 0; i < toCheck; ++i) {
      TRACE('   - fetching #', i, '/', toCheck, '(', countsA, '|', BOUNTY_MAX_OFFSETS_TO_TRACK, ')');
      let offset = bounty_getOffset(bounty, indexA, i);
      TRACE('   - #' + i, ', offset =', offset);
      if (offset !== impOffset) {
        let op = ml_dec8(ml, offset);
        if (op === ML_ISALL) {
          TRACE(' - Found the isall...');
          if (_trick_implhs_isall_2shared(impOffset, offset, indexA, indexB)) return true;
        }
      }
    }

    TRACE(' - end of trick_implhs_isall_2shared');
    return false;
  }
  function _trick_implhs_isall_2shared(impOffset, isallOffset, indexA, indexB) {
    // A -> B, A = all?(B C D ...)     =>    drop imp
    TRACE(' - _trick_implhs_isall_2shared; A -> B, A = all?(B C D ...)    =>    drop imp');

    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'should be isall');
    //TRACE(ml__debug(ml, isallOffset, 1, problem, true));
    let argCount = ml_dec16(ml, isallOffset + 1);
    let indexR = readIndex(ml, isallOffset + SIZEOF_C + argCount * 2);
    TRACE('     - isall with an argCount of', argCount, ', indexR=', indexR, '=indexA=', indexA, ', cross-checking all args to match', indexB);
    ASSERT(indexA === indexR, 'A should be R, should be asserted by bounty');

    // scan for any arg index == B
    for (let i = 0; i < argCount; ++i) {
      let argIndex = readIndex(ml, isallOffset + SIZEOF_C + i * 2);
      if (argIndex === indexB) {
        TRACE_MORPH('R -> A, R = all?(A ...)', 'R = all?(A ...)', 'The isall subsumes the implication');
        TRACE('     - arg index is indexB, match. this is R -> A, R = all?(A ...) so eliminate the imp');
        ml_eliminate(ml, impOffset, SIZEOF_C_2);
        bounty_markVar(bounty, indexA);
        bounty_markVar(bounty, indexB);
        somethingChanged();
        return true;
      }
    }
    return false;
  }

  function trick_isall_lterhs_entry(indexS, lteOffset, counts) {
    // A <= S, S = all?(B C...)    ->    A <= B, A <= C

    let offset1 = bounty_getOffset(bounty, indexS, 0);
    let offset2 = bounty_getOffset(bounty, indexS, 1);
    TRACE('trick_isall_lterhs_entry; ', indexS, 'at', lteOffset, '->', offset1, offset2, '` A <= S, S = all?(B C...)    ->    A <= B, A <= C`');
    ASSERT(lteOffset === offset1 || lteOffset === offset2, 'expecting current offset to be one of the two offsets found', lteOffset, indexS);

    let isallOffset = lteOffset === offset1 ? offset2 : offset1;

    // this stuff should have been checked by the bounty hunter, so we tuck them in ASSERTs
    ASSERT(ml_dec8(ml, lteOffset) === ML_LTE, 'lteOffset should be an lte');
    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'isall offset should be either isall op');
    ASSERT(getMeta(bounty, indexS) === (BOUNTY_FLAG_LTE_RHS | BOUNTY_FLAG_ISALL_RESULT), 'kind of redundant, but this is what bounty should have yielded for this var');
    ASSERT(counts === 2, 'S should only appear in two constraints');
    ASSERT((ml_dec8(ml, isallOffset) === ML_ISALL ? readIndex(ml, isallOffset + SIZEOF_C + ml_dec16(ml, isallOffset + 1) * 2) : readIndex(ml, isallOffset + 5)) === indexS, 'S should the result of the isall');

    // we can replace an isall and lte with ltes on the args of the isall
    // A <= S, S = isall(C D)   ->    A <= C, A <= D

    // note that A amust be strict bool and A must have a 0 for this to be safe. S is our shared var here.
    // [01] <= [01], [01] = isall(....)

    // if you dont apply this condition:
    // [0 0 5 5 9 9] <= [0 0 9 9], [0 0 9 9] = isall([55], [66])
    // after the morph A _must_ be 0 or 5 while before it could also be 9.

    let indexA = readIndex(ml, lteOffset + OFFSET_C_A);
    let A = getDomain(indexA, true);
    ASSERT(indexS === readIndex(ml, lteOffset + OFFSET_C_B), 'S should be rhs of lte');
    let S = getDomain(indexS, true);

    // mostly A will be [01] but dont rule out valid cases when A=0 or A=1
    // A or C (or both) MUST be boolean bound or this trick may be bad (A=100,S=100,C=1,D=1 -> 100<=10,100<=10 while it should pass)

    if (domain_max(A) > 1 && domain_max(S) > 1) {
      TRACE(' - neither A nor S was boolean bound, bailing', domain__debug(A), domain__debug(S));
      return false;
    }

    if (domain_hasNoZero(S)) {
      // (dead code because minifier should eliminate an isall when R>=1)
      TRACE('- S has no zero which it would need to reflect any solution as a leaf, bailing', domain__debug(S));
      // (unless the isall was already solved, but the minimizer should take care of that)
      requestAnotherCycle = true;
      return false;
    }

    if (domain_max(A) > domain_max(S)) {
      // (dead code because minifier should eliminate an isall when R=0)
      TRACE(' - max(A) > max(S) so there is a value in A that S couldnt satisfy A<=S so we must bail', domain__debug(A), domain__debug(S));
      // we can only trick if S can represent any valuation of A and there is a reject possible so no
      // note that this shouldnt happen when the minimizer runs to the max, but could in single cycle mode
      requestAnotherCycle = true;
      return false;
    }

    TRACE(' - A and S are okay proceeding with morph, A:', domain__debug(A), 'S:', domain__debug(S));

    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'bounty should have asserted this');

    let argCount = ml_dec16(ml, isallOffset + 1);
    TRACE(' - an isall starting at', isallOffset, 'and has', argCount, 'args; rewriting A <= S, S=isall(X Y Z ...)  ->  A <= X, A <= Y, A <= Z, ...');

    let maxA = domain_max(A);
    for (let i = 0; i < argCount; ++i) {
      let index = readIndex(ml, isallOffset + SIZEOF_C + i * 2);
      let domain = getDomain(index, true);
      if (domain_max(domain) < maxA) {
        TRACE(' - there is an isall arg whose max is lower than max(A), this leads to a lossy morph so we must bail', i, index, domain__debug(domain), '<', domain__debug(A));
        return false;
      }
    }

    if (argCount < 2) {
      TRACE(' - argcount < 2, so a bug or an alias. ignoring that here. bailing');
      return false;
    }

    // first encode the isall args beyond the second one (if any) into recycled spaces
    if (argCount > 2) {
      let proceed = trick_isall_lterhs_entry_excess(ml, isallOffset, argCount, indexA, isallArgs);
      if (!proceed) return false;
    }

    // now morph the first two args into the existing lte and isall (of same size)
    let indexX = readIndex(ml, isallOffset + OFFSET_C_A);
    let indexY = readIndex(ml, isallOffset + OFFSET_C_B);

    TRACE(' -  A <= S, S=isall(X Y, ...(already done the rest))   ->    A <= X, A <= Y');

    // must mark all affected vars. their bounty data is probably obsolete now.
    // (collect the isall before morphing it!)
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexS);
    let isallArgs = markAndCollectArgs(ml, isallOffset, argCount);
    ASSERT(isallArgs[0] === indexX, 'x should be collected');
    ASSERT(isallArgs[1] === indexY, 'y should be collected');

    TRACE(' - isall args:', isallArgs, ', and from the lte A=', indexA, ', S=', indexS);

    // compile A<=left and A<=right over the existing two offsets
    ml_c2c2(ml, lteOffset, 2, ML_LTE, indexA, indexX);
    ml_cr2c2(ml, isallOffset, 2, ML_LTE, indexA, indexY);

    TRACE('   - deferring', indexS, 'will be gt', indexA, 'and the result of an isall');
    solveStack.push((_, force, getDomain, setDomain) => {
      // note: we cut out indexS so that's what we restore here!
      TRACE(' - trick_isall_lterhs_entry; patching index', indexS);
      TRACE('   -', indexA, '<=', indexS, '  ->  ', domain__debug(getDomain(indexA)), '<=', domain__debug(getDomain(indexS)));
      TRACE('   -', indexS, '= all?(', isallArgs, ')  ->  ', domain__debug(getDomain(indexS)), '= all?(', isallArgs.map(index => domain__debug(getDomain(index))), ')');

      let S = getDomain(indexS);
      let A = getDomain(indexA);

      // was A <= S so S can't contain any value lower than max(A)
      S = domain_removeLtUnsafe(S, domain_max(A));
      ASSERT(S, 'should not be empty here');

      // was S = isall(X Y ...args) so force any arg that is not yet booly-solved until we find one that's 0
      let someZero = false;
      for (let i = 0; i < isallArgs.length; ++i) {
        let D = getDomain(isallArgs[i]);
        if (domain_isZero(D) || (!domain_hasNoZero(S) && force(D) === 0)) {
          TRACE('  - index', isallArgs[i], 'was', domain__debug(D), 'now', domain__debug(getDomain(isallArgs[i])), ', ends up zero so it fails the isall so S must be 0');
          // either D was already zero, or it was booly and then forced to zero. it fails the isall so S=0
          someZero = true;
          break;
        }
      }
      TRACE(' -', someZero ? 'at least one' : 'no', 'arg was found to be zero');
      if (someZero) {
        S = domain_removeGtUnsafe(S, 0);
      } else {
        S = domain_removeValue(S, 0);
      }
      ASSERT(S, 'S should not be empty here');
      setDomain(indexS, S);
    });

    somethingChanged();
    return true;
  }
  function trick_isall_lterhs_entry_excess(ml, isallOffset, argCount, indexA) {
    // isall has four or more args
    // A <= S, S=isall(X Y Z ...)  ->  A <= X, A <= Y, A <= Z, ...
    // note: this function only compiles the args from Z (the third isall arg) onward
    TRACE(' - trick_isall_lterhs_entry_excess. Attempting to recycle space to stuff', argCount - 2, 'lte constraints');
    ASSERT(argCount > 2, 'this function should only be called for 4+ isall args');

    // we have to recycle some space now. we wont know whether we can
    // actually do the morph until we've collected enough space for it.

    // we'll use lteOffset and isallOffset to compile the last 2 args so only need space for the remaining ones
    let toRecycle = argCount - 2;

    // start by collecting toRecycle recycled spaces
    let bins = ml_getRecycleOffsets(ml, 0, toRecycle, SIZEOF_C_2);
    if (!bins) {
      TRACE(' - Was unable to find enough free space to fit', argCount, 'ltes, bailing');
      return false;
    }

    TRACE(' - Found', bins.length, 'jumps (', bins, ') which can host (at least)', toRecycle, 'lte constraints. Compiling them now');

    // okay, now we'll morph. be careful about clobbering existing indexes... start with
    // last address to make sure jumps dont clobber existing jump offsets in the bin

    let i = 0;
    while (i < toRecycle) {
      let currentOffset = bins.pop();
      ASSERT(ml_dec8(ml, currentOffset) === ML_JMP, 'should only get jumps here'); // might trap a case where we clobber
      let size = ml_getOpSizeSlow(ml, currentOffset);
      ASSERT(size >= SIZEOF_C_2, 'this is what we asked for');
      do {
        let indexB = readIndex(ml, isallOffset + SIZEOF_C + (i + 2) * 2); // note: i+2 because we skip the first two args. they are done by caller
        TRACE('  - compiling lte:', indexA, '<=', indexB, ' -> ', domain__debug(getDomain(indexA, true)), '<=', domain__debug(getDomain(indexB, true)));

        ml_enc8(ml, currentOffset, ML_LTE);
        ml_enc16(ml, currentOffset + 1, 2);
        ml_enc16(ml, currentOffset + OFFSET_C_A, indexA);
        ml_enc16(ml, currentOffset + OFFSET_C_B, indexB);

        ++i;
        size -= SIZEOF_C_2;
        currentOffset += SIZEOF_C_2;
      } while (size >= SIZEOF_C_2 && i < toRecycle);
      if (size) ml_compileJumpSafe(ml, currentOffset, size);
      ASSERT(!void ml_validateSkeleton(ml), 'trick_isall_lterhs_entry_excess compiling ltes'); // cant check earlier
    }

    return true;
  }

  function trick_imprhs_isall_entry(indexS, impOffset, countsS, indexA) {
    // A -> S, S = all?(B C...)    =>    A -> B, A -> C

    let offset1 = bounty_getOffset(bounty, indexS, 0);
    let offset2 = bounty_getOffset(bounty, indexS, 1);
    TRACE('trick_imprhs_isall_entry; ', indexS, 'at', impOffset, '=>', offset1, offset2, '`; A -> S, S = all?(B C...)    =>    A -> B, A -> C`');
    ASSERT(impOffset === offset1 || impOffset === offset2, 'expecting current offset to be one of the two offsets found', impOffset, indexS);

    let isallOffset = impOffset === offset1 ? offset2 : offset1;

    // this stuff should have been checked by the bounty hunter, so we tuck them in ASSERTs
    ASSERT(ml_dec8(ml, impOffset) === ML_IMP, 'impOffset should be an imp');
    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'isall offset should be either isall op');
    ASSERT(getMeta(bounty, indexS) === (BOUNTY_FLAG_IMP_RHS | BOUNTY_FLAG_ISALL_RESULT), 'kind of redundant, but this is what bounty should have yielded for this var');
    ASSERT(countsS === 2, 'S should only appear in two constraints');
    ASSERT((ml_dec8(ml, isallOffset) === ML_ISALL ? readIndex(ml, isallOffset + SIZEOF_C + ml_dec16(ml, isallOffset + 1) * 2) : readIndex(ml, isallOffset + 5)) === indexS, 'S should the result of the isall');
    ASSERT(readIndex(ml, impOffset + OFFSET_C_A) === indexA, 'A should be lhs of IMP');

    // we can replace an isall and IMP with IMPs on the args of the isall
    // A -> S, S = isall(C D)    =>     A -> C, A -> D

    // note that A must be strict bool and A must have a 0 for this to be safe. S is our shared var here.
    // [01] -> [01], [01] = isall(....)

    // if you dont apply this condition:
    // [0 0 5 5 9 9] -> [0 0 9 9], [0 0 9 9] = isall([55], [66])
    // after the morph A _must_ be 0 or 5 while before it could also be 9.

    let A = getDomain(indexA, true);
    ASSERT(indexS === readIndex(ml, impOffset + OFFSET_C_B), 'S should be rhs of IMP');
    let S = getDomain(indexS, true);

    // mostly A will be [01] but dont rule out valid cases when A=0 or A=1

    if (domain_max(A) > 1 && domain_max(S) > 1) {
      TRACE(' - neither A nor S was boolean bound, bailing', domain__debug(A), domain__debug(S));
      return false;
    }

    if (domain_hasNoZero(S)) {
      // (dead code because minifier should eliminate an isall when R>=1)
      TRACE('- S has no zero which it would need to reflect any solution as a leaf, bailing', domain__debug(S));
      // (unless the isall was already solved, but the minimizer should take care of that)
      requestAnotherCycle = true;
      return false;
    }

    if (domain_max(A) > domain_max(S)) {
      // (dead code because minifier should eliminate an isall when R=0)
      TRACE(' - max(A) > max(S) so there is a value in A that S couldnt satisfy A->S so we must bail', domain__debug(A), domain__debug(S));
      // we can only trick if S can represent any valuation of A and there is a reject possible so no
      // note that this shouldnt happen when the minimizer runs to the max, but could in single cycle mode
      requestAnotherCycle = true;
      return false;
    }

    TRACE(' - A and S are okay proceeding with morph, ', domain__debug(A), '->', domain__debug(S));

    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'bounty should have asserted this');

    let argCount = ml_dec16(ml, isallOffset + 1);
    TRACE(' - an isall starting at', isallOffset, 'and has', argCount, 'args; rewriting A -> S, S=isall(X Y Z ...)  =>  A -> X, A -> Y, A -> Z, ...');

    if (argCount < 2) {
      TRACE(' - argcount < 2, so a bug or an alias. ignoring that here. bailing');
      requestAnotherCycle = true; // minifier should tear this down
      return false;
    }

    // first encode the isall args beyond the second one (if any) into recycled spaces
    if (argCount > 2) {
      let proceed = trick_imprhs_isall_entry_excess(ml, isallOffset, argCount, indexA, isallArgs);
      if (!proceed) return false;
    }

    // now morph the first two args into the existing IMP and isall (of same size)
    let indexX = readIndex(ml, isallOffset + OFFSET_C_A);
    let indexY = readIndex(ml, isallOffset + OFFSET_C_B);

    TRACE(' -  A -> S, S=isall(X Y, ...(already done the rest))   =>    A -> X, A -> Y');

    // must mark all affected vars. their bounty data is probably obsolete now.
    // (collect the isall before morphing it!)
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexS);
    let isallArgs = markAndCollectArgs(ml, isallOffset, argCount);
    ASSERT(isallArgs[0] === indexX, 'x should be collected');
    ASSERT(isallArgs[1] === indexY, 'y should be collected');

    TRACE(' - isall args:', isallArgs, ', and from the IMP A=', indexA, ', S=', indexS);

    // compile A->left and A->right over the existing two offsets
    ml_c2c2(ml, impOffset, 2, ML_IMP, indexA, indexX);
    ml_cr2c2(ml, isallOffset, argCount, ML_IMP, indexA, indexY);

    TRACE('   - deferring', indexS, 'will be gt', indexA, 'and the result of an isall');
    solveStack.push((_, force, getDomain, setDomain) => {
      // note: we cut out indexS so that's what we restore here!
      TRACE(' - trick_imprhs_isall_entry; patching index', indexS);
      TRACE('   -', indexA, '->', indexS, '  =>  ', domain__debug(getDomain(indexA)), '->', domain__debug(getDomain(indexS)));
      TRACE('   -', indexS, '= all?(', isallArgs, ')  =>  ', domain__debug(getDomain(indexS)), '= all?(', isallArgs.map(index => domain__debug(getDomain(index))), ')');

      let S = getDomain(indexS);
      let A = getDomain(indexA);

      TRACE(' - must first scan whether S ought to be set or unset according to the other imp/isall args');

      // check whether S is forced at all by the imp or isall
      let isSet = false;
      let isUnset = false;

      TRACE(' - A->S so if A is set, S must be set; A>0?', domain_hasNoZero(A));
      if (domain_hasNoZero(A)) {
        TRACE(' - A is set so S must be set');
        isSet = true;
      }

      TRACE(' - check the "set" state of all args');
      let allSet = true;
      for (let i = 0; i < argCount; ++i) {
        let index = isallArgs[i];
        let D = getDomain(index);
        TRACE('    - index:', index, ', D:', domain__debug(D));
        if (domain_isZero(D)) {
          TRACE('    - isall had an arg that was zero so S must be zero');
          isUnset = true;
          allSet = false;
          break;
        } else if (domain_hasZero(D)) {
          TRACE('    - isall had at least one arg that wasnt set yet so the isall does not force S to be set, at least');
          allSet = false;
        }
      }
      if (allSet) {
        TRACE(' - all args of the isall were set so S must be set');
        isSet = true;
      }

      TRACE(' - result of scan: set?', isSet, ', unset?', isUnset);
      ASSERT(!(isSet && isUnset), 'shouldnt be both set and unset');
      let result = false;
      if (isSet) {
        setDomain(indexS, domain_removeValue(S, 0));
        result = true;
      } else if (isUnset) {
        setDomain(indexS, domain_removeGtUnsafe(S, 0));
        result = false;
      } else {
        result = force(indexS) > 0;
        TRACE(' - forced S to', result);
      }

      TRACE(' - now apply the state of S=', (result ? 1 : 0), ' to the other args');
      TRACE('   -', domain__debug(getDomain(indexA)), '->', (result ? 1 : 0));
      TRACE('   -', (result ? 1 : 0), '= all?(', isallArgs.map(index => domain__debug(getDomain(index))), ')');

      // A -> S so if S=0 then A=0
      if (!result) {
        TRACE(' - A->S, S=0 so A=0');
        setDomain(indexA, domain_removeGtUnsafe(A, 0));
      }

      let found = false;
      for (let i = 0; i < argCount; ++i) {
        let index = isallArgs[i];
        let D = getDomain(index);
        if (result) { // true=isall(...D) so D>0
          TRACE(' - S>0 so all args must be >0');
          setDomain(index, domain_removeValue(D, 0));
        } else if (domain_isZero(D)) {
          found = true;
          break;
        } else if (domain_hasZero(D)) { // false=isall(...D) so D=0
          TRACE(' - S=0 so one arg must be 0');
          setDomain(index, domain_removeGtUnsafe(D, 0));
          found = true;
          break;
        }
      }

      TRACE(' - final result:');
      TRACE('   -', domain__debug(getDomain(indexA)), '->', (result ? 1 : 0));
      TRACE('   -', (result ? 1 : 0), '= all?(', isallArgs.map(index => domain__debug(getDomain(index))), ')');

      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexS));
      ASSERT(!isallArgs.some(index => !getDomain(index)));
      ASSERT(domain_hasNoZero(getDomain(indexA)) ? domain_hasNoZero(getDomain(indexS)) : 1);
      ASSERT(domain_isZero(getDomain(indexS)) ? domain_isZero(getDomain(indexA)) : 1);
      ASSERT(domain_isSolved(getDomain(indexS)));
      ASSERT(domain_isZero(getDomain(indexS)) === isallArgs.some(index => domain_isZero(getDomain(index))));
      ASSERT(result || found, 'if result is false at least one arg should be false');
    });

    somethingChanged();
    return true;
  }
  function trick_imprhs_isall_entry_excess(ml, isallOffset, argCount, indexA) {
    // isall has four or more args
    // A -> S, S=isall(X Y Z ...)  =>  A -> X, A -> Y, A -> Z, ...
    // note: this function only compiles the args from Z (the third isall arg) onward
    TRACE(' - trick_imprhs_isall_entry_excess. Attempting to recycle space to stuff', argCount - 2, 'IMP constraints');
    ASSERT(argCount > 2, 'this function should only be called for 3+ isall args');

    // we have to recycle some space now. we wont know whether we can
    // actually do the morph until we've collected enough space for it.

    // we'll use impOffset and isallOffset to compile the last 2 args so only need space for the remaining ones
    let toRecycle = argCount - 2;

    // start by collecting toRecycle recycled spaces
    let bins = ml_getRecycleOffsets(ml, 0, toRecycle, SIZEOF_C_2);
    if (!bins) {
      TRACE(' - Was unable to find enough free space to fit', argCount, 'IMPs, bailing');
      return false;
    }

    TRACE(' - Found', bins.length, 'jumps (', bins, ') which can host (at least)', toRecycle, 'IMP constraints. Compiling them now');

    // okay, now we'll morph. be careful about clobbering existing indexes... start with
    // last address to make sure jumps dont clobber existing jump offsets in the bin

    let i = 0;
    while (i < toRecycle) {
      let currentOffset = bins.pop();
      ASSERT(ml_dec8(ml, currentOffset) === ML_JMP, 'should only get jumps here'); // might trap a case where we clobber
      let size = ml_getOpSizeSlow(ml, currentOffset);
      ASSERT(size >= SIZEOF_C_2, 'this is what we asked for');
      do {
        let indexB = readIndex(ml, isallOffset + SIZEOF_C + (i + 2) * 2); // note: i+2 because we skip the first two args. they are done by caller
        TRACE('  - compiling IMP:', indexA, '->', indexB, ' -> ', domain__debug(getDomain(indexA, true)), '->', domain__debug(getDomain(indexB, true)));

        ml_enc8(ml, currentOffset, ML_IMP);
        ml_enc16(ml, currentOffset + 1, 2);
        ml_enc16(ml, currentOffset + OFFSET_C_A, indexA);
        ml_enc16(ml, currentOffset + OFFSET_C_B, indexB);

        ++i;
        size -= SIZEOF_C_2;
        currentOffset += SIZEOF_C_2;
      } while (size >= SIZEOF_C_2 && i < toRecycle);
      if (size) ml_compileJumpSafe(ml, currentOffset, size);
      ASSERT(!void ml_validateSkeleton(ml), 'trick_imprhs_isall_entry_excess compiling IMPs'); // cant check earlier
    }

    return true;
  }

  function trick_issame_lterhs(indexR, lteOffset, countsR, indexC) {
    TRACE('trick_issame_lterhs');
    TRACE('   - R = A ==? B, C <= R    =>       R = A ==? B, C -> R');
    TRACE('   - (if the requirements hold it only morphs an lte to an imp)');

    ASSERT(countsR === 2, 'should be leaf var');

    // prerequisites: all bools, R leaf (the latter has been confirmed)

    let offset1 = bounty_getOffset(bounty, indexR, 0);
    let offset2 = bounty_getOffset(bounty, indexR, 1);
    let issameOffset = offset1 === lteOffset ? offset2 : offset1;

    ASSERT(ml_dec8(ml, issameOffset) === ML_ISSAME, 'should be issame');
    ASSERT(readIndex(ml, issameOffset + OFFSET_C_R) === indexR, 'issame result should be R');
    if (ml_dec16(ml, issameOffset + 1) !== 2) {
      TRACE(' - isall does not have 2 args, bailing');
      return false;
    }

    let indexA = readIndex(ml, issameOffset + OFFSET_C_A);
    let indexB = readIndex(ml, issameOffset + OFFSET_C_B);

    let A = getDomain(indexA, true);
    let B = getDomain(indexB, true);
    let C = getDomain(indexC, true);
    let R = getDomain(indexR, true);
    TRACE(' - domains; A=', domain__debug(A), ', B=', domain__debug(B), ', C=', domain__debug(C), ', R=', domain__debug(R));
    if (!domain_isBool(A) || !domain_isBool(B) || !domain_isBool(C) || !domain_isBool(R)) {
      TRACE(' - at least one of the three domains isnt bool, bailing');
      return false;
    }

    // okay. morph the lte into implication
    TRACE(' - morphing, R = A ==? B, C <= R      =>       R = A ==? B, C -> R');

    ml_c2c2(ml, lteOffset, 2, ML_IMP, indexC, indexR);
    // dont mark A or B because we did not change their ops
    bounty_markVar(bounty, indexC);
    bounty_markVar(bounty, indexR);
    somethingChanged();
    return true;
  }

  function trick_isall_nall_2shared(ml, indexR, isallOffset, counts) {
    // R = all?(A B), nall(R A D)   ->    R = all?(A B), R !& D

    let offset1 = bounty_getOffset(bounty, indexR, 0);
    let offset2 = bounty_getOffset(bounty, indexR, 1);

    TRACE('trick_isall_nall_2shared', indexR, 'at', isallOffset, 'and', offset1, '/', offset2, 'metaFlags:', getMeta(bounty, indexR, true), '`R = all?(A B), nall(R A D)`   ->    `R = all?(A B), R !& D`');

    let nallOffset = offset1 === isallOffset ? offset2 : offset1;
    let argCountNall = ml_dec16(ml, nallOffset + 1);
    let argCountIsall = ml_dec16(ml, isallOffset + 1);

    // this stuff should have been checked by the bounty hunter, so we tuck them in ASSERTs
    ASSERT(getMeta(bounty, indexR) === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_ISALL_RESULT), 'the var should only be part of a nall and the result of an isall');
    ASSERT(counts === 2, 'R should only appear in two constraints');
    ASSERT(isallOffset === offset1 || isallOffset === offset2, 'expecting current offset to be one of the two offsets found', isallOffset, indexR);
    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'isall offset should be an isall');
    ASSERT(ml_dec8(ml, nallOffset) === ML_NALL, 'other offset should be a nall');
    ASSERT(getAlias(indexR) === indexR, 'should be unaliased');
    ASSERT(readIndex(ml, isallOffset + SIZEOF_C + argCountIsall * 2) === indexR, 'var should be R of isall');

    // this should be `R = all?(A B ...), nall(R A D)`
    // if R = 1 then A and B (etc) are 1, so the nall will have two 1's, meaning D must be 0
    // if R = 0 then the nall is already satisfied. neither the nall nor the isall is redundant
    // because `R !& D` must be maintained, so remove the shared arg from the nall

    if (argCountNall !== 3) {
      TRACE(' - fingerprint didnt match (', argCountNall, ' !== 3) so bailing');
      return false;
    }

    // (this is kind of dead code since isall1 wont get 2 args and that's required for this trick)
    TRACE(' - nall has 3 args, check if it shares an arg with the isall');
    // next; one of the two isalls must occur in the nall
    // R = all?(A B), nall(R A C)
    // R = all?(A B), nall(X Y Z)

    // nall args
    let indexX = readIndex(ml, nallOffset + SIZEOF_C);
    let indexY = readIndex(ml, nallOffset + SIZEOF_C + 2);
    let indexZ = readIndex(ml, nallOffset + SIZEOF_C + 4);
    TRACE(' - nall(' + [indexX, indexY, indexZ] + ') -> nall(', [domain__debug(getDomain(indexX, true)), domain__debug(getDomain(indexY)), domain__debug(getDomain(indexZ))], ')');

    for (let i = 0; i < argCountIsall; ++i) {
      let argIndex = readIndex(ml, isallOffset + SIZEOF_C + i * 2);
      if (argIndex === indexX) return _updateNallForTrick(ml, nallOffset, indexY, indexZ, indexX);
      if (argIndex === indexY) return _updateNallForTrick(ml, nallOffset, indexX, indexZ, indexY);
      if (argIndex === indexZ) return _updateNallForTrick(ml, nallOffset, indexX, indexY, indexZ);
    }

    TRACE(' - no shared args');
    return false;
  }
  function _updateNallForTrick(ml, offset, indexA, indexB, indexDropped) {
    TRACE(' - isall arg matches an arg of nall. dropping it from the nall');
    // since we know the nall has 3 args we can simply write the two args we want and a noop for the last position
    // keep A and B, the other index is dropped because we're writing a noop in its place

    ASSERT(ml_dec8(ml, offset) === ML_NALL, 'should be nall');
    ASSERT(ml_dec16(ml, offset + 1) === 3, 'nall should have 3 args');

    ml_enc16(ml, offset + 1, 2); // down from 3 to 2 args
    ml_enc16(ml, offset + OFFSET_C_A, indexA);
    ml_enc16(ml, offset + OFFSET_C_B, indexB);
    ml_enc8(ml, offset + OFFSET_C_C, ML_NOOP2);
    // this only affected the nall and its args so no need to mark the isall vars
    bounty_markVar(bounty, indexDropped);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    somethingChanged();
    return true;
  }

  function trick_ltelhs_nall_leaf(ml, indexA, countsA) {
    // A <= B, A !& C   ->   A leaf, all constraints dropped. for _any_ lte_lhs / nall

    TRACE('trick_ltelhs_nall_leaf; bounty A:', bounty__debug(bounty, indexA));
    TRACE(' - indexA=', indexA, '; `A <= B, A !& C   ->   nothing (for any number of LTE_LHS and NAND ops).');
    TRACE('   - A=', domain__debug(getDomain(indexA)), '; if it has a zero it can never break LTE_LHS or NALL');

    // rationale; assuming A has at least a zero, there's no valuation of B or C that could lead to breaking
    // the <= or !& constraints. so A can still be considered a leaf var.
    // note that the number of args of the NALL is irrelevant

    ASSERT(getMeta(bounty, indexA) === BOUNTY_FLAG_LTE_LHS || getMeta(bounty, indexA) === BOUNTY_FLAG_NALL || getMeta(bounty, indexA) === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_LTE_LHS), 'the var should only be lhs of LTEs or part of NALLs');
    ASSERT(getAlias(indexA) === indexA, 'should be unaliased');

    // TODO: what if there aren't any NALLs? then A could still be a leaf even if it was nonzero

    // A must contain zero for this to work for else it may not solve the nall
    if (domain_hasNoZero(getDomain(indexA, true))) {
      TRACE(' - A contains no zero, bailing');
      return false;
    }

    // no need for further verification.

    TRACE(' - marking LTE/NALL args, eliminating the constraints');
    for (let i = 0; i < countsA; ++i) {
      let offset = bounty_getOffset(bounty, indexA, i);
      let opCode = ml_dec8(ml, offset);
      TRACE('    - next op:', ml__debug(ml, offset, 1, problem));
      if (opCode === ML_LTE) {
        ASSERT(readIndex(ml, offset + OFFSET_C_A) === indexA, 'A should (at least) be LTE_LHS');
        ASSERT(readIndex(ml, offset + 1) === 2, 'LTE is assumed to always have 2 args');

        let index = readIndex(ml, offset + OFFSET_C_B);
        if (index !== indexA) {
          bounty_markVar(bounty, index);
          ml_eliminate(ml, offset, SIZEOF_C_2);
        }
      } else if (opCode === ML_NALL) {
        let argCount = readIndex(ml, offset + 1);
        for (let j = 0; j < argCount; ++j) {
          let index = readIndex(ml, offset + SIZEOF_C + j * 2);
          if (index !== indexA) {
            bounty_markVar(bounty, index);
          }
        }
        ml_eliminate(ml, offset, SIZEOF_C + argCount * 2);
      } else {
        ASSERT(false, 'bounty should have asserted A to only be LTE_LHS and NALL so this cant happen?');
        TRACE(' - the unthinkable happened, bailing'); // *shrug* it's not a problem to throw for
        return false;
      }
    }

    // note: We could go through great lengths in an effort to reduce A as little as possible but since
    // this trick involves any number of NALLs and LTEs, this leads to a bunch of difficult checks and
    // heuristics. And even then we're still very likely to set A to zero anyways.
    // Let's save us the code head ache here and just do it now.

    TRACE(' - setting A to zero for the sake of simplicity');
    let A = getDomain(indexA, true);
    let nA = domain_removeGtUnsafe(A, 0);
    if (A !== nA) setDomain(indexA, nA);
    bounty_markVar(bounty, indexA);

    somethingChanged();
    return true;
  }

  function trick_implhs_nall_leaf(ml, indexA, countsA) {
    // for all A, A -> B, A !& C   =>   cut A, all constraints dropped. for _any_ imp_lhs / nall on A

    TRACE('trick_implhs_nall_leaf');
    TRACE(' - indexA=', indexA, ', bounty A:', bounty__debug(bounty, indexA));
    TRACE_MORPH('A -> B, A !& C', '', '(for any number of IMP_LHS and NAND ops).');
    TRACE('   - A=', domain__debug(getDomain(indexA)), '; if it has a zero it can never break IMP_LHS or NALL');

    // rationale; assuming A has at least a zero, there's no valuation of B or C that could lead to breaking
    // the -> or !& constraints. so A can still be considered a leaf var.
    // note that the number of args of the NALL is irrelevant

    ASSERT(getMeta(bounty, indexA) === BOUNTY_FLAG_IMP_LHS || getMeta(bounty, indexA) === BOUNTY_FLAG_NALL || getMeta(bounty, indexA) === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_IMP_LHS), 'the var should only be lhs of IMPs or part of NALLs');
    ASSERT(getAlias(indexA) === indexA, 'should be unaliased');

    // TODO: what if there aren't any NALLs? then A could still be a leaf even if it was nonzero

    // A must contain zero for this to work for else A may not solve the nall
    if (domain_hasNoZero(getDomain(indexA, true))) {
      TRACE(' - A contains no zero, bailing');
      requestAnotherCycle = true;
      return false;
    }

    // no need for further verification.
    // A is only the IMP_LHS or NALL arg
    // if we set it to 0 here then those immediately solve
    // we could go into great code complexity here handling everything nicely
    // or we could just set it to 0 here and request another run. oh yes.

    TRACE_MORPH('A -> B, A !& C', 'A=0', 'this will solve all implications and nalls');
    TRACE(' - setting A to zero for the sake of simplicity');
    let A = getDomain(indexA, true);
    if (!domain_isZero(A)) {
      let nA = domain_removeGtUnsafe(A, 0);
      if (A !== nA) setDomain(indexA, nA);
      bounty_markVar(bounty, indexA);
    }

    somethingChanged(); // this will require another minimizer as well
    return true;
  }

  function trick_ltelhs_some_leaf(ml, lteOffset, indexA, countsA) {
    // A <= B, A | C   =>   B | C, A leaf

    TRACE('trick_ltelhs_some_leaf');
    TRACE(' - A <= B, some(A C ...)     =>     some(B C ...), A leaf');

    let A = getDomain(indexA, true);
    TRACE(' - indexA=', indexA, ', =', domain__debug(A));

    ASSERT(getMeta(bounty, indexA) === (BOUNTY_FLAG_LTE_LHS | BOUNTY_FLAG_SOME), 'A is leaf on an LTE and SOME');
    ASSERT(getAlias(indexA) === indexA, 'should be unaliased');
    ASSERT(countsA === 2, 'should have 2 offsets');

    if (!domain_isBool(A)) {
      TRACE(' - A wasnt a bool, bailing');
      return false;
    }

    let indexB = readIndex(ml, lteOffset + OFFSET_C_B);
    let B = getDomain(indexB, true);
    if (!domain_isBool(B)) {
      TRACE(' - B wasnt a bool, bailing');
      return false;
    }

    TRACE(' - constraints verified, applying trick');
    TRACE_MORPH('A <= B, some(A C ...)', 'some(B C ...)', 'A is leaf');

    let offset1 = bounty_getOffset(bounty, indexA, 0);
    let offset2 = bounty_getOffset(bounty, indexA, 1);
    let someOffset = offset1 === lteOffset ? offset2 : offset1;

    ASSERT(ml_dec8(ml, someOffset) === ML_SOME);
    // note: arg count of the SOME is not important. A must simply be part of it (and bounty asserted that already)
    let argCount = ml_dec16(ml, someOffset + 1);

    let args = markAndCollectArgs(ml, someOffset, argCount, indexA);

    ml_eliminate(ml, lteOffset, SIZEOF_C_2);
    ml_cx2cx(ml, someOffset, argCount, ML_SOME, [indexB].concat(args));

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - trick_ltelhs_some_leaf');
      TRACE(' - A <= B, some(A C ...)    =>     some(B C ...)');

      let A = getDomain(indexA);
      let B = getDomain(indexB);

      let nA = A;

      // ensure A<=B
      if (domain_max(nA) > domain_min(B)) {
        nA = domain_removeGtUnsafe(nA, domain_min(B));
      }
      // ensure the SOME holds
      if (!domain_isZero(nA)) {
        let removeZero = true; // without other args, A must be nonzero to satisfy the SOME
        for (let i = 0, len = args.length; i < len; ++i) {
          let index = args[i];
          let D = getDomain(index);
          if (domain_hasNoZero(D)) { // at least one arg already satisfies the SOME
            break;
          }
          if (domain_isBooly(D)) {
            removeZero = true; // at least one arg is undetermined so to make sure its value is irrelevant we set A>0
            break;
          }
          removeZero = false;
        }
        if (removeZero) {
          nA = domain_removeValue(nA, 0);
        }
      }

      ASSERT(nA, 'A should hold all values');
      if (A !== nA) setDomain(indexA, nA);
    });

    bounty_markVar(bounty, indexA);

    somethingChanged();
    return true;
  }

  function trick_implhs_some_leaf(ml, impOffset, indexA, countsA) {
    // A -> B, A | C   =>   B | C, A leaf

    TRACE('trick_implhs_some_leaf');
    TRACE(' - A -> B, some(A C ...)     =>     some(B C ...), A leaf');

    let A = getDomain(indexA, true);
    TRACE(' - indexA=', indexA, ', =', domain__debug(A));

    ASSERT(getMeta(bounty, indexA) === (BOUNTY_FLAG_IMP_LHS | BOUNTY_FLAG_SOME), 'A is leaf on an IMP and SOME');
    ASSERT(getAlias(indexA) === indexA, 'should be unaliased');
    ASSERT(countsA === 2, 'should have 2 offsets');

    if (!domain_isBool(A)) {
      TRACE(' - A wasnt a bool, bailing');
      return false;
    }

    let indexB = readIndex(ml, impOffset + OFFSET_C_B);
    let B = getDomain(indexB, true);
    if (!domain_isBool(B)) {
      TRACE(' - B wasnt a bool, bailing');
      return false;
    }

    TRACE(' - constraints verified, applying trick');
    TRACE_MORPH('A -> B, some(A C ...)', 'some(B C ...)', 'A is leaf');

    let offset1 = bounty_getOffset(bounty, indexA, 0);
    let offset2 = bounty_getOffset(bounty, indexA, 1);
    let someOffset = offset1 === impOffset ? offset2 : offset1;

    ASSERT(ml_dec8(ml, someOffset) === ML_SOME);
    // note: arg count of the SOME is not important. A must simply be part of it (and bounty asserted that already)
    let argCount = ml_dec16(ml, someOffset + 1);

    let args = markAndCollectArgs(ml, someOffset, argCount, indexA);

    ml_eliminate(ml, impOffset, SIZEOF_C_2);
    ml_cx2cx(ml, someOffset, argCount, ML_SOME, [indexB].concat(args));

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - trick_implhs_some_leaf');
      TRACE(' - A -> B, some(A C ...)    =>     some(B C ...)');

      let A = getDomain(indexA);
      let B = getDomain(indexB);

      let nA = A;

      // ensure A->B
      if (domain_hasNoZero(B)) {
        nA = domain_removeValue(nA, 0);
      } else {
        nA = domain_removeGtUnsafe(nA, 0);
      }
      // ensure the SOME holds
      if (!domain_isZero(nA)) {
        let removeZero = true; // without other args, A must be nonzero to satisfy the SOME
        for (let i = 0, len = args.length; i < len; ++i) {
          let index = args[i];
          let D = getDomain(index);
          if (domain_hasNoZero(D)) { // at least one arg already satisfies the SOME
            break;
          }
          if (domain_isBooly(D)) {
            removeZero = true; // at least one arg is undetermined so to make sure its value is irrelevant we set A>0
            break;
          }
          removeZero = false;
        }
        if (removeZero) {
          nA = domain_removeValue(nA, 0);
        }
      }

      ASSERT(nA, 'A should hold all values');
      if (A !== nA) setDomain(indexA, nA);
    });

    bounty_markVar(bounty, indexA);

    somethingChanged();
    return true;
  }

  function trick_imp_islte_c_v(islteOffset, indexR, indexA, indexB, countsR) {
    TRACE('trick_imp_islte_c_v');
    TRACE(' - R = A <=? B, B -> R, solved(A)  =>  R = A <=? B');

    // first search for the imp offset
    for (let i = 0; i < countsR; ++i) {
      let offset = bounty_getOffset(bounty, indexR, i);
      if (offset !== islteOffset) {
        let op = ml_dec8(ml, offset);
        if (op === ML_IMP) {
          if (readIndex(ml, offset + OFFSET_C_A) === indexB && readIndex(ml, offset + OFFSET_C_B) === indexR) {
            return _trick_imp_islte_c_v(indexR, indexA, indexB, islteOffset, offset);
          }
        }
      }
    }
    ASSERT(false, 'bounty should have asserted this imp exists');
    return false;
  }
  function _trick_imp_islte_c_v(indexR, indexA, indexB, islteOffset, impOffset) {
    TRACE(' - _trick_imp_islte_c_v; R = A <=? B, B -> R   =>   R !^ B, remove [1..A-1] from B');
    ASSERT(domain_isSolved(getDomain(indexA)));

    // note:
    // - if R=0 then B->R then B->0 then 0->0 so B=0
    // - if R>0 then B->R always holds and R=vA<=?B holds when B>=vA
    // - if vA<=min(B) then R>0 because vA cannot be >B
    // - if vA>max(B) then R=0 because vA cannot be <=B
    // so R !^ B and remove from B all values from 1 up to but not including vA


    // [01] = 2 <=? [02], [02] -> [01]
    // R=0
    // => 0 = 2 <=? [02], [02] -> 0
    // => 2 > [02], [02] -> 0
    // => 2 > 0, 0 -> 0
    // R>0
    // => 1 = 2 <=? [02], [02] -> 1
    // => 2 <= [02], [02] -> 1
    // => 2 <= 2, 2 -> 1

    // [01] = 5 <=? [09], [09] -> [01]
    // R=0
    // => 0 = 2 <=? [09], [09] -> 0
    // => 2 > [09], [09] -> 0
    // => 2 > [01], [01] -> 0
    // => 2 > 0, 0 -> 0
    // R>0
    // => 1 = 2 <=? [09], [09] -> 1
    // => 2 <= [09], [09] -> 1
    // => 2 <= [29], [29] -> 1

    let A = getDomain(indexA, true);
    let B = getDomain(indexB, true);
    let vA = domain_getValue(A);

    TRACE(' - first checking;', vA, '<=', domain_min(B), ' and ', vA, '>', domain_max(B));

    if (vA <= domain_min(B)) {
      // R>0 because if R=0 then A>B and that's not possible
      // let minimizer take this down
      TRACE(' - A<=min(B) means R>0, minimizer can solve this, bailing');
      requestAnotherCycle = true;
      return false;
    }

    if (vA > domain_max(B)) {
      TRACE(' - A > max(B), minimizer can solve this, bailing');
      requestAnotherCycle = true;
      return false;
    }

    TRACE_MORPH('R = A <=? B, B -> R', 'R !^ B, remove [1..A-1] from B');
    TRACE(' - indexes: A=', indexA, ', B=', indexB, ', R=', indexR);
    TRACE(' - domains: A=', domain__debug(getDomain(indexA)), ', B=', domain__debug(getDomain(indexB)), ', R=', domain__debug(getDomain(indexR)));

    // create a mask that removes 1..A then intersect B with that mask (because B may already be missing more values)
    let mask = domain_arrToSmallest([0, 0, vA, domain_max(B)]);
    let nB = domain_intersection(B, mask);
    TRACE(' - B mask:', domain__debug(mask), ', B after mask:', domain__debug(mask)); // probably the same
    if (B !== nB) {
      setDomain(indexB, nB);
      if (!nB) return emptyDomain = true;
    }

    ml_c2c2(ml, impOffset, 2, ML_XNOR, indexR, indexB);
    ml_eliminate(ml, islteOffset, SIZEOF_VVV);

    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    somethingChanged();
    return true;
  }

  function trick_imp_islte_v_c(islteOffset, indexR, indexA, indexB, countsR) {
    TRACE('trick_imp_islte_c_v');
    TRACE(' - R = A <=? B, A -> R, solved(B)  =>  R > 0, A <= B');

    // first search for the imp offset
    for (let i = 0; i < countsR; ++i) {
      let offset = bounty_getOffset(bounty, indexR, i);
      if (offset !== islteOffset) {
        let op = ml_dec8(ml, offset);
        if (op === ML_IMP) {
          if (readIndex(ml, offset + OFFSET_C_A) === indexA && readIndex(ml, offset + OFFSET_C_B) === indexR) {
            return _trick_imp_islte_v_c(indexR, indexA, indexB, islteOffset, offset);
          }
        }
      }
    }
    ASSERT(false, 'bounty should have asserted this imp exists');
    return false;
  }
  function _trick_imp_islte_v_c(indexR, indexA, indexB, islteOffset, impOffset) {
    TRACE(' - _trick_imp_islte_c_v');
    ASSERT(domain_isSolved(getDomain(indexB)));

    // note:
    // - if R=0 then A > vB then A>0 then A->R so R>0 then falsum
    // - if R>0 then A <= vB then A->R always holds because R>0
    // - so R>0, islte becomes lte, imp is eliminated

    let R = getDomain(indexR, true);
    R = domain_removeValue(R, 0);
    if (!R) {
      emptyDomain = true;
      return false;
    }

    let A = getDomain(indexA, true);
    let B = getDomain(indexB, true);
    if (domain_getValue(B) <= domain_min(A)) {
      TRACE(' - B <= min(A), minimizer can solve this, bailing');
      requestAnotherCycle = true;
      return false;
    }

    TRACE_MORPH('R = A <=? B, A -> R', 'R > 0, A <= B');
    TRACE(' - indexes: A=', indexA, ', B=', indexB, ', R=', indexR);
    TRACE(' - domains: A=', domain__debug(getDomain(indexA)), ', B=', domain__debug(getDomain(indexB)), ', R=', domain__debug(getDomain(indexR)));

    setDomain(indexR, R);
    ml_c2c2(ml, impOffset, 2, ML_LTE, indexA, indexB);
    ml_eliminate(ml, islteOffset, SIZEOF_VVV);

    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    somethingChanged();
    return true;
  }

  function trick_only_ltelhs_leaf(ml, indexA, countsA) {
    TRACE('trick_only_ltelhs_leaf; bounty A:', bounty__debug(bounty, indexA));
    TRACE(' - A should only be an LTE_LHS for any number of LTE ops. cut it as a leaf and eliminate constraints');

    // there is no way A breaks any LTEs unless there's already an rhs var that is smaller than it
    // no need to check here. just go.

    let A = getDomain(indexA, true);

    let rhsArgs = [];
    for (let i = 0; i < countsA; ++i) {
      let offset = bounty_getOffset(bounty, indexA, i);
      TRACE('    - next op:', ml__debug(ml, offset, 1, problem));
      ASSERT(ml_dec8(ml, offset) === ML_LTE);
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'all LTE have 2 args');
      ASSERT(readIndex(ml, offset + OFFSET_C_A) === indexA, 'A should be the lhs');
      let indexB = readIndex(ml, offset + OFFSET_C_B);
      if (domain_max(getDomain(indexB)) < domain_min(A)) {
        TRACE(' indexB=', indexB, 'and it is already smaller than A;', domain__debug(A), '>', domain__debug(getDomain(indexB)));
        TRACE(' constraint cant hold, empty domain, rejecting');
        setDomain(indexB, 0);
        return true; // "true" as in "something awful happened"
      }
      rhsArgs.push(indexB);
      ml_eliminate(ml, offset, SIZEOF_C_2);
    }

    TRACE(' - Adding solve stack entry');
    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - trick_only_ltelhs_leaf; shaving A to pass all LTEs');

      let A = getDomain(indexA);
      let nA = A;
      for (let i = 0, il = rhsArgs.length; i < il; ++i) {
        let indexB = rhsArgs[i];
        TRACE('   - removing everything >', domain_min(getDomain(indexB)), 'from', domain__debug(nA));
        nA = domain_removeGtUnsafe(nA, domain_min(getDomain(indexB)));
      }
      ASSERT(nA, 'A should be able to be <= all the index B args');
      if (A !== nA) setDomain(indexA, nA);
    });

    bounty_markVar(bounty, indexA);
    for (let i = 0, il = rhsArgs.length; i < il; ++i) {
      bounty_markVar(bounty, rhsArgs[i]);
    }
    somethingChanged();
    return true;
  }

  function trick_only_implhs_leaf(ml, indexA, countsA) {
    TRACE('trick_only_implhs_leaf; bounty A:', bounty__debug(bounty, indexA));
    TRACE(' - A should only be an IMP_LHS for any number of IMP ops. confirm none of the Bs are zero. then cut it as a leaf and eliminate constraints');

    let A = getDomain(indexA, true);
    if (domain_isZero(A) || domain_hasNoZero(A)) {
      TRACE(' - A is not a booly. implication is resolved, let minimizer take care of it, bailing');
      requestAnotherCycle = true; // force minimizer to take care of this one
      return false;
    }

    // the only way A breaks any IMPs is if it has an rhs that is zero. so check that first.
    for (let i = 0; i < countsA; ++i) {
      let offset = bounty_getOffset(bounty, indexA, i);
      TRACE('    - next op:', ml__debug(ml, offset, 1, problem));
      ASSERT(ml_dec8(ml, offset) === ML_IMP);
      ASSERT(readIndex(ml, offset + OFFSET_C_A) === indexA, 'A should be the lhs');
      let indexB = readIndex(ml, offset + OFFSET_C_B);
      if (domain_isZero(indexB)) {
        TRACE(' - indexB=', indexB, 'and is already zero;', domain__debug(A), '->', domain__debug(getDomain(indexB)));
        TRACE(' - implication is resolved, let minimizer take care of it, bailing');
        requestAnotherCycle = true; // force minimizer to take care of this one
        return false;
      }
    }

    TRACE_MORPH('A -> B, A -> C, ...', 'A==0', 'leaf A, they dont break implication now so the implication cant break A once the rhs solves');

    let rhsArgs = [];
    for (let i = 0; i < countsA; ++i) {
      let offset = bounty_getOffset(bounty, indexA, i);
      let indexB = readIndex(ml, offset + OFFSET_C_B);
      rhsArgs.push(indexB);
      ml_eliminate(ml, offset, SIZEOF_C_2);
    }

    // TODO: could potentially improve "force" choice here but A=0 is definitely the simplest play
    TRACE(' - forcing A to 0 since thats the most likely outcome anyways and the safest play here');

    let nA = domain_intersectionValue(A, 0);
    ASSERT(nA !== A, 'since A was confirmed to be a booly before it should be different now');
    ASSERT(nA, 'since A was a booly we should be able to set it to 0');
    setDomain(indexA, nA);

    bounty_markVar(bounty, indexA);
    for (let i = 0, il = rhsArgs.length; i < il; ++i) {
      bounty_markVar(bounty, rhsArgs[i]);
    }
    somethingChanged();
    return true;
  }

  function trick_isall_nall_1shared(ml, indexR, isallOffset, countsR) {
    // R = all?(A B ...), R !& C  ->  nall(A B ... C)
    // note: this works for any nalls on one isall
    TRACE('trick_isall_nall_1shared;', indexR, '`R = all?(A B), R !& C  ->  nall(A B C)` for any nall on one isall, any arg count for either');

    // this stuff should have been checked by the bounty hunter, so we tuck them in ASSERTs
    ASSERT(getMeta(bounty, indexR) === (BOUNTY_FLAG_NALL | BOUNTY_FLAG_ISALL_RESULT), 'the var should only be nall[2] and isall', bounty__debugMeta(bounty, indexR), countsR);
    ASSERT(ml_dec8(ml, isallOffset) === ML_ISALL, 'isall offset should be an isall');
    ASSERT(getAlias(indexR) === indexR, 'should be unaliased');
    ASSERT(readIndex(ml, isallOffset + SIZEOF_C + ml_dec16(ml, isallOffset + 1) * 2) === indexR, 'R should be result of isall');
    ASSERT(countsR < BOUNTY_MAX_OFFSETS_TO_TRACK, 'counts should not exceed maxed tracked');

    let isallArgCount = ml_dec16(ml, isallOffset + 1);
    let isallSizeof = SIZEOF_C + isallArgCount * 2 + 2;
    let isallArgs = [];
    for (let i = 0; i < isallArgCount; ++i) {
      let index = readIndex(ml, isallOffset + SIZEOF_C + i * 2);
      isallArgs.push(index);
    }

    TRACE(' - trick_isall_nall_1shared; first confirming all other offsets are nalls with 2 args; isall arg count:', isallArgCount, ', isall args:', isallArgs);

    let nalls = 0;
    for (let i = 0; i < countsR; ++i) {
      let nallOffset = bounty_getOffset(bounty, indexR, i);
      ASSERT(nallOffset, 'there should be as many offsets as counts unless that exceeds the max and that has been checked already');
      if (nallOffset !== isallOffset) {
        let opcode = ml_dec8(ml, nallOffset);
        if (opcode !== ML_NALL) {
          TRACE(' - found at least one other isall, bailing');
          ASSERT(opcode === ML_ISALL, 'bounty should have asserted that the offsets can only be isall and nall');
          return false;
        }
        if (ml_dec16(ml, nallOffset + 1) !== 2) {
          TRACE(' - found a nall that did not have 2 args, bailing for now');
          return false;
        }
        ++nalls;
      }
      ASSERT(nallOffset === isallOffset || readIndex(ml, nallOffset + OFFSET_C_A) === indexR || readIndex(ml, nallOffset + OFFSET_C_B) === indexR, 'R should be part of the nall');
    }

    // bounty asserted that all these nalls contain R, rewrite each such nall

    TRACE(' - trick_isall_nall_1shared; there are', nalls, 'nalls; for each nall: `X !& B, X = all?(C D)`   ->   `nall(B C D)`');
    TRACE(' - one nall will fit inside the isall but any others need recycled spaces (because the existing nalls have 2 args)');

    // each nall with 2 args becomes a nall with all the isall args + 1, that should be at least 3
    let sizeofNall = SIZEOF_C + (isallArgCount + 1) * 2;

    let nallSpacesNeeded = nalls - 1; // -1 because we can always recycle the original isall
    TRACE(' - isall offset=', isallOffset, ', size(isall)=', isallSizeof, ', size(nall)=', sizeofNall, ', there are', nalls, 'nalls[2] and each morphs into a nall[' + isallSizeof + '] so we need', nallSpacesNeeded, 'spaces');
    ASSERT(isallSizeof === sizeofNall, 'both isalls should be a cr-op so should have enough space for this nall');

    let bins;
    if (nallSpacesNeeded) {
      TRACE(' - need additional space; searching for', nallSpacesNeeded, 'spaces of size=', sizeofNall);
      bins = ml_getRecycleOffsets(ml, 0, nallSpacesNeeded, sizeofNall);
      if (!bins) {
        TRACE(' - Was unable to find enough free space to fit', nalls, 'nalls, bailing');
        return false;
      }
    }

    // if any of the nall args or any of the isall args is 0, then so is R. so collect all args together to defer R
    let allArgs = isallArgs.slice(0);

    let offsetCounter = 0;
    let rewrittenNalls = 0; // only used in ASSERTs, minifier should eliminate this

    if (nallSpacesNeeded) {
      TRACE(' - starting to morph', nallSpacesNeeded, 'nalls into bins');
      ml_recycles(ml, bins, nallSpacesNeeded, sizeofNall, (recycledOffset, i, sizeLeft) => {
        TRACE('   - using: recycledOffset:', recycledOffset, ', i:', i, ', sizeLeft:', sizeLeft);

        let offset;
        do {
          if (offsetCounter >= countsR) {
            TRACE(' - (last offset must have been offset)');
            return true;
          }
          offset = bounty_getOffset(bounty, indexR, offsetCounter++);
          TRACE('     - offset', offset, 'is isall?', offset === isallOffset);
        } while (offset === isallOffset);

        TRACE('     - offset', offset, 'is not isall so it should be nall');
        ASSERT(ml_dec8(ml, offset) === ML_NALL, 'should be nall');
        ASSERT(offset, 'the earlier loop counted the nalls so it should still have that number of offsets now');
        ASSERT(sizeLeft === ml_getOpSizeSlow(ml, recycledOffset), 'size left should be >=size(op)');
        _trick_isall_nall_1shared_CreateNallAndRemoveNall(ml, indexR, isallArgs.slice(0), allArgs, offset, recycledOffset, sizeLeft);
        ASSERT(++rewrittenNalls);

        return false;
      });
      ASSERT(rewrittenNalls === nallSpacesNeeded, 'should have processed all offsets for R', rewrittenNalls, '==', nallSpacesNeeded, '(', offsetCounter, countsR, ')');
      TRACE(' - all nalls should be morphed now');
    }

    // now recycle the isall. have to do it afterwards because otherwise the found recycled bins may be clobbered
    // when eliminating the nall. there's no test for this because it's rather complex to create. sad.
    TRACE(' - recycling the old isall into the last nall');
    let lastNallOffset = bounty_getOffset(bounty, indexR, offsetCounter++);
    if (lastNallOffset === isallOffset) lastNallOffset = bounty_getOffset(bounty, indexR, offsetCounter++);
    _trick_isall_nall_1shared_CreateNallAndRemoveNall(ml, indexR, isallArgs.slice(0), allArgs, lastNallOffset, isallOffset, isallSizeof);
    ASSERT(++rewrittenNalls);

    TRACE('   - deferring', indexR, 'will be R = all?(', allArgs, ')');
    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - trick_isall_nall_1shared;', indexR, '= all?(', allArgs, ')  ->  ', domain__debug(getDomain(indexR)), '= all?(', allArgs.map(index => domain__debug(getDomain(index))), ')');

      let R = getDomain(indexR);
      allArgs.some(index => {
        let X = getDomain(index);
        if (!domain_hasNoZero(X)) { // if non-zero, this var wont affect R
          let vX = force(index);
          if (vX === 0) {
            R = domain_removeGtUnsafe(R, 0);
            return true;
          }
        }
      });
      // R should be updated properly now. basically if any arg solved to zero, it will be zero. otherwise unchanged.

      ASSERT(R, 'R should have at least a value to solve left');
      setDomain(indexR, R);
    });

    bounty_markVar(bounty, indexR);
    for (let i = 0, l = allArgs.length; i < l; ++i) {
      bounty_markVar(bounty, allArgs[i]);
    }

    return true;
  }
  function _trick_isall_nall_1shared_CreateNallAndRemoveNall(ml, indexR, nallArgs, allArgs, nallOffset, recycleOffset, recycleSizeof) {
    TRACE(' - _trick_isall_nall_1shared_CreateNallAndRemoveNall: indexR:', indexR, 'nallArgs:', nallArgs, 'allArgs:', allArgs, 'nallOffset:', nallOffset, 'recycleOffset:', recycleOffset, 'recycleSizeof:', recycleSizeof);

    ASSERT(ml_dec16(ml, nallOffset + 1) === 2, 'nalls should have 2 args');

    let indexX = readIndex(ml, nallOffset + OFFSET_C_A);
    let indexY = readIndex(ml, nallOffset + OFFSET_C_B);
    ASSERT(indexX === indexR || indexY === indexR, 'expecting indexR to be part of the nall');
    let index = indexX === indexR ? indexY : indexX;
    TRACE(' - other nall index is', index, domain__debug(getDomain(index, true)));

    nallArgs.push(index);
    allArgs.push(index);

    // note: bounty_markVar happens at caller
    TRACE(' - writing a new nall');
    ml_any2c(ml, recycleOffset, recycleSizeof, ML_NALL, nallArgs);
    if (nallOffset !== recycleOffset) {
      TRACE(' - removing the nall because we didnt recycle it');
      ml_eliminate(ml, nallOffset, SIZEOF_C_2);
    }
    ASSERT(ml_validateSkeleton(ml, '_trick_isall_nall_1shared_CreateNallAndRemoveNall'));
  }

  function trick_diff_elimination(diffOffset, indexX, countsX, indexY) {
    // bascially we "invert" one arg by aliasing it to the other arg and then inverting all ops that relate to it

    // the case with multiple diffs should be eliminated elsewhere
    // all targeted ops should only have 2 args
    // see also the xor elimination (similar to this one)

    // A <= X, X != Y    ->    A !& Y
    // X <= A, X != Y    ->    A | Y
    // X | A, X != Y     ->    Y <= A
    // X !& A, X != Y    ->    A <= Y
    // A -> X, X != Y    ->    A !& Y
    // X -> A, X != Y    ->    A | Y

    TRACE('trick_diff_elimination');
    TRACE(' - index:', indexX, '^', indexY);
    TRACE(' - domains:', domain__debug(getDomain(indexX)), '!=', domain__debug(getDomain(indexY)));
    TRACE(' - meta:', bounty__debugMeta(bounty, indexX), '!=', bounty__debugMeta(bounty, indexY));
    TRACE(' - verying; looking for one DIFF[2], `X != Y` and then we can morph any of these;');
    TRACE('   - LTE_LHS:   X != Y, X <= A     =>    A | Y');
    TRACE('   - LTE_RHS:   X != Y, A <= X     =>    A !& Y');
    TRACE('   - SOME:      X != Y, X | A      =>    Y <= A    =>    Y -> A');
    TRACE('   - NALL:      X != Y, X !& A     =>    A <= Y    =>    A -> Y');
    TRACE('   - IMP_LHS:   X != Y, X -> A     =>    Y | A');
    TRACE('   - IMP_RHS:   X != Y, A -> X     =>    A !& Y');

    // first we need to validate. we can only have one diff and all ops can only have 2 args
    ASSERT(countsX < BOUNTY_MAX_OFFSETS_TO_TRACK, 'this was already checked in cut_diff');
    ASSERT(ml_dec16(ml, diffOffset + 1) === 2, 'the diff should be confirmed to have 2 args');

    if (!domain_isBoolyPair(getDomain(indexX))) {
      TRACE(' - X is non-bool, bailing');
      return false;
    }

    // we need the offsets to eliminate them and to get the "other" var index for each
    let lteLhsOffsets = [];
    let lteLhsArgs = [];
    let lteRhsOffsets = [];
    let lteRhsArgs = [];
    let someOffsets = [];
    let someArgs = [];
    let nallOffsets = [];
    let nallArgs = [];
    let seenDiff = false;
    let diffArgs = [];
    let impLhsOffsets = [];
    let impLhsArgs = [];
    let impRhsOffsets = [];
    let impRhsArgs = [];
    TRACE(' - scanning', countsX, 'offsets now..');
    for (let i = 0; i < countsX; ++i) {
      let offset = bounty_getOffset(bounty, indexX, i);
      ASSERT(offset, 'the offset should exist...', offset);

      let op = ml_dec8(ml, offset);
      TRACE('   - pos=', i, ', offset=', offset, 'op=', ml__opName(op));

      ASSERT(op === ML_LTE || op === ML_DIFF || op === ML_SOME || op === ML_NALL || op === ML_IMP, 'should be one of these four ops, bounty said so', ml__opName(op));

      if (ml_dec16(ml, offset + 1) !== 2) {
        TRACE(' - op does not have 2 args, bailing');
        return false;
      }

      let indexA = readIndex(ml, offset + OFFSET_C_A);
      let indexB = readIndex(ml, offset + OFFSET_C_B);
      let A = getDomain(indexA, true);
      let B = getDomain(indexB, true);
      ASSERT(indexA === indexX || indexB === indexX, 'bounty should only track ops that use target var');
      if (!domain_isBoolyPair(indexA === indexX ? B : A)) {
        TRACE(' - found an op with a non-bool arg, bailing');
        return false;
      }
      let indexC = indexA === indexX ? indexB : indexA;

      if (op === ML_LTE) {
        // A ^ B, A <= C
        // [00022]^[01],[0022]<=[01]  what if B must end up zero?
        // we have to make sure the lte constraint can not possibly be broken at this point
        if (domain_max(A) > domain_max(B) || domain_min(B) < domain_min(A)) {
          TRACE(' - there are valuations of A and B that could break LTE, bailing because minimizer can fix this');
          requestAnotherCycle = true;
          return false;
        }
        if (indexA === indexX) {
          lteLhsOffsets.push(offset);
          lteLhsArgs.push(indexC);
        } else {
          lteRhsOffsets.push(offset);
          lteRhsArgs.push(indexC);
        }
      } else if (op === ML_IMP) {
        if (indexA === indexX) {
          impLhsOffsets.push(offset);
          impLhsArgs.push(indexC);
        } else {
          impRhsOffsets.push(offset);
          impRhsArgs.push(indexC);
        }
      } else if (op === ML_DIFF) {
        if (diffOffset !== offset) {
          TRACE(' - found a different DIFF, this trick only works on one, bailing');
          return false;
        }
        ASSERT(indexC === indexY);
        diffArgs.push(indexC);
        seenDiff = true;
      } else if (op === ML_SOME) {
        someOffsets.push(offset);
        someArgs.push(indexC);
      } else {
        ASSERT(op === ML_NALL, 'see assert above');
        nallOffsets.push(offset);
        nallArgs.push(indexC);
      }
    }

    TRACE(' - collection complete; indexY =', indexY, ', diff offset =', diffOffset, ', lte lhs offsets:', lteLhsOffsets, ', lte rhs offsets:', lteRhsOffsets, ', SOME offsets:', someOffsets, ', nall offsets:', nallOffsets, ', imp lhs offsets:', impLhsOffsets, ', imp rhs offsets:', impRhsOffsets);

    ASSERT(seenDiff, 'should have seen a diff, bounty said there would be one');

    // okay. pattern matches. do the rewrite

    TRACE(' - pattern confirmed, morphing ops, removing diff');
    TRACE('   - X != Y, X <= A     =>    A | Y');
    TRACE('   - X != Y, A <= X     =>    A !& Y');
    TRACE('   - X != Y, X | A      =>    Y <= A    =>    Y -> A');
    TRACE('   - X != Y, X !& A     =>    A <= Y    =>    A -> Y');
    TRACE('   - X != Y, X -> A     =>    Y | A');
    TRACE('   - X != Y, A -> X     =>    A !& Y');

    TRACE_MORPH('X != Y', '', 'inverting LTE, SOME, NALL, IMP');

    TRACE(' - processing', lteLhsOffsets.length, 'LTE_LHS ops');
    for (let i = 0, len = lteLhsOffsets.length; i < len; ++i) {
      TRACE_MORPH('X <= A, X != Y', 'A | Y');
      let offset = lteLhsOffsets[i];
      let index = readIndex(ml, offset + OFFSET_C_A);
      if (index === indexX) index = readIndex(ml, offset + OFFSET_C_B);
      bounty_markVar(bounty, index);
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, offset, 2, ML_SOME, index, indexY);
    }

    TRACE(' - processing', lteRhsOffsets.length, 'LTE_RHS ops');
    for (let i = 0, len = lteRhsOffsets.length; i < len; ++i) {
      TRACE_MORPH('X <= A, X != Y', 'A | Y');
      let offset = lteRhsOffsets[i];
      let index = readIndex(ml, offset + OFFSET_C_A);
      if (index === indexX) index = readIndex(ml, offset + OFFSET_C_B);
      bounty_markVar(bounty, index);
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, offset, 2, ML_NALL, index, indexY);
    }

    // note: this bit is kind of redundant (and untested) because it's rewritten and picked up elsewhere
    TRACE(' - processing', someOffsets.length, 'SOME ops');
    for (let i = 0, len = someOffsets.length; i < len; ++i) {
      TRACE_MORPH('X | A, X != Y', 'Y <= A');
      let offset = someOffsets[i];
      let index = readIndex(ml, offset + OFFSET_C_A);
      if (index === indexX) index = readIndex(ml, offset + OFFSET_C_B);
      bounty_markVar(bounty, index);
      ASSERT(ml_dec8(ml, offset) === ML_SOME, 'right?');
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, offset, 2, ML_LTE, indexY, index);
    }

    TRACE(' - processing', nallOffsets.length, 'NALL ops');
    for (let i = 0, len = nallOffsets.length; i < len; ++i) {
      TRACE_MORPH('X !& A, X != Y', 'A <= Y');
      let offset = nallOffsets[i];
      let index = readIndex(ml, offset + OFFSET_C_A);
      if (index === indexX) index = readIndex(ml, offset + OFFSET_C_B);
      bounty_markVar(bounty, index);
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, offset, 2, ML_LTE, index, indexY);
    }

    TRACE(' - processing', impLhsOffsets.length, 'IMP_LHS ops');
    for (let i = 0, len = impLhsOffsets.length; i < len; ++i) {
      TRACE_MORPH('X -> A, X != Y', 'A | Y');
      let offset = impLhsOffsets[i];
      let index = readIndex(ml, offset + OFFSET_C_A);
      if (index === indexX) index = readIndex(ml, offset + OFFSET_C_B);
      bounty_markVar(bounty, index);
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, offset, 2, ML_SOME, index, indexY);
    }

    TRACE(' - processing', impRhsOffsets.length, 'IMP_RHS ops');
    for (let i = 0, len = impRhsOffsets.length; i < len; ++i) {
      TRACE_MORPH('X -> A, X != Y', 'A | Y');
      let offset = impRhsOffsets[i];
      let index = readIndex(ml, offset + OFFSET_C_A);
      if (index === indexX) index = readIndex(ml, offset + OFFSET_C_B);
      bounty_markVar(bounty, index);
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, offset, 2, ML_NALL, index, indexY);
    }

    TRACE(' - and finally removing the DIFF');
    ASSERT(ml_dec16(ml, diffOffset + 1) === 2, 'diff should have 2 args here');
    ml_eliminate(ml, diffOffset, SIZEOF_C_2);

    TRACE(' - X is a leaf constraint, defer it', indexX);
    leafs.push(indexX);
    solveStack.push((_, force, getDomain, setDomain) => {
      let X = getDomain(indexX);
      let Y = getDomain(indexY);
      TRACE(' - diff + ops...;', indexX, '!=', indexY, '  ->  ', domain__debug(X), '!=', domain__debug(getDomain(indexY)));


      //TRACE(' - X:',domain__debug(X));
      //TRACE(' - Y:',domain__debug(getDomain(indexY)));
      //TRACE(' - ltelhs:', lteLhsArgs.map(a=>domain__debug(getDomain(a))));
      //TRACE(' - lterhs:', lteRhsArgs.map(a=>domain__debug(getDomain(a))));
      //TRACE(' - some:', someArgs.map(a=>domain__debug(getDomain(a))));
      //TRACE(' - nall:', nallArgs.map(a=>domain__debug(getDomain(a))));
      //TRACE(' - implhs:', impLhsArgs.map(a=>domain__debug(getDomain(a))));
      //TRACE(' - imprhs:', impRhsArgs.map(a=>domain__debug(getDomain(a))));

      let oX = X;

      let minX = domain_min(X);
      let maxX = domain_max(X);

      TRACE('  - applying', lteLhsArgs.length, 'LTELHSs (X <= vars)');
      for (let i = 0; i < lteLhsArgs.length; ++i) {
        // X <= D
        let index = lteLhsArgs[i];
        let D = getDomain(index);
        TRACE('    - index:', index, ', domain:', domain__debug(D));
        let minD = domain_min(D);
        if (maxX > minD) {
          let maxD = domain_max(D);
          // at least one value of X is larger than a value in D so there is currently
          // a valuation of X and D that violates the LTE and we must fix that.
          if (maxD >= maxX) {
            // there are values in D that are larger-eq to all values in X. use them.
            // just remove the intersecting values from D and then lte should satisfy
            D = domain_removeLtUnsafe(D, maxX);
            setDomain(index, D);
          } else {
            // the largest value of D is smaller than the largest X
            // maximize D then remove any value from X larger than that
            D = domain_intersectionValue(D, maxD);
            setDomain(index, D);
            X = domain_removeGtUnsafe(X, maxD);
          }
          ASSERT(D);
          ASSERT(X);
          ASSERT(domain_max(X) <= domain_min(D));
        }
      }
      TRACE('   - X after LTELHSs:', domain__debug(X));

      TRACE('  - applying', lteRhsArgs.length, 'LTERHSs (vars <= X)');
      for (let i = 0; i < lteRhsArgs.length; ++i) {
        // D <= X
        let index = lteRhsArgs[i];
        let D = getDomain(index);
        TRACE('    - index:', index, ', domain:', domain__debug(D));
        let maxD = domain_max(D);
        if (minX < maxD) {
          // at least one value in X is smaller than a value in D so there is currently
          // a valuation of X and D that violates the LTE and we must fix that.
          let minD = domain_min(D);
          if (minD <= minX) {
            // there are values in D that are smaller-eq to all values in X. use them.
            // just remove the intersecting values from D and then lte should satisfy
            D = domain_removeGtUnsafe(D, minX);
            setDomain(index, D);
          } else {
            // the smallest value of D is larger than the smallest X
            // minimze D then remove any value from X smaller than that
            D = domain_intersectionValue(D, minD);
            setDomain(index, D);
            X = domain_removeLtUnsafe(X, maxD);
          }
        }
        ASSERT(D);
        ASSERT(X);
        ASSERT(domain_max(D) <= domain_min(X));
      }
      TRACE('   - X after LTERHSs:', domain__debug(X));

      // reminder: these are pairs. some(X D) for each d in someArgs
      for (let i = 0; i < someArgs.length; ++i) {
        // some(X ...)
        let index = someArgs[i];
        let D = getDomain(index);
        TRACE('    - index:', index, ', domain:', domain__debug(getDomain(index)));
        if (domain_isZero(D)) {
          // X must be nonzero now
          X = domain_removeValue(X, 0);
        } else if (domain_hasZero(D)) {
          ASSERT(domain_isBooly(D), 'assuming D isnt empty, and it wasnt zero but has a zero, it should be a booly');
          D = domain_removeValue(D, 0);
          setDomain(index, D);
        }
        ASSERT(X);
        ASSERT(D);
        ASSERT(domain_hasNoZero(X) || domain_hasNoZero(D));
      }
      TRACE('   - X after SOMEs:', domain__debug(X));

      // reminder: these are pairs. nall(X D) for each d in nallArgs
      for (let i = 0; i < nallArgs.length; ++i) {
        // nall(X ...)
        let index = nallArgs[i];
        let D = getDomain(index);
        TRACE('    - index:', index, ', domain:', domain__debug(D));
        if (domain_hasNoZero(D)) {
          // X must be zero
          X = domain_removeGtUnsafe(X, 0);
        } else if (domain_hasNoZero(D)) {
          ASSERT(domain_isBooly(D), 'assuming D isnt empty, and it wasnt nonzero, it should be a booly');
          D = domain_removeGtUnsafe(D, 0);
          setDomain(index, D);
        }
        ASSERT(X);
        ASSERT(D);
        ASSERT(domain_isZero(X) || domain_isZero(D));
      }
      TRACE('   - X after NALLs:', domain__debug(X));

      for (let i = 0; i < impLhsArgs.length; ++i) {
        // X -> D
        let index = impLhsArgs[i];
        let D = getDomain(index);
        TRACE('    - index:', index, ', domain:', domain__debug(D));

        // the easiest out is that D is either nonzero or that X is zero
        if (!domain_hasNoZero(D) && !domain_isZero(X)) {
          if (domain_isZero(D)) {
            // X must be zero otherwise the implication doesnt hold
            X = domain_removeGtUnsafe(X, 0);
          } else if (domain_hasNoZero(D)) {
            // X must be nonzero because D is nonzero
            X = domain_removeValue(X, 0);
          } else {
            ASSERT(domain_isBooly(D));
            // setting D to nonzero is the safest thing to do
            setDomain(index, domain_removeValue(D, 0));
          }
        }
        ASSERT(X);
        ASSERT(D);
        ASSERT(domain_hasNoZero(X) ? domain_hasNoZero(D) : true);
        ASSERT(domain_isZero(D) ? domain_isZero(X) : true);
        ASSERT(domain_isSolved(D) || domain_isZero(X), 'if X is zero then D doesnt matter. if D is solved then X is asserted to be fine above');
      }
      TRACE('   - X after IMPLHSs:', domain__debug(X));

      for (let i = 0; i < impRhsArgs.length; ++i) {
        // D -> X
        let index = impRhsArgs[i];
        let D = getDomain(index);
        TRACE('    - index:', index, ', domain:', domain__debug(D));

        if (domain_hasNoZero(D)) {
          // X must be nonzero
          X = domain_removeGtUnsafe(X, 0);
        } else if (domain_isBooly(D)) {
          // safest value for imp-lhs is 0
          D = domain_removeValue(D, 0);
        }
        ASSERT(X);
        ASSERT(D);
        ASSERT(domain_hasNoZero(D) ? domain_hasNoZero(X) : true);
        ASSERT(domain_isZero(X) ? domain_isZero(D) : true);
        ASSERT(domain_isSolved(X) || domain_isZero(D), 'if D is zero then X doesnt matter. if X is solved then D is asserted to be fine above');
      }
      TRACE('   - X after IMPRHSs:', domain__debug(X));

      // X != Y
      TRACE(' - != Y:', domain__debug(getDomain(indexY)));
      if (domain_isSolved(X)) {
        Y = domain_removeValue(Y, domain_getValue(X));
        setDomain(indexY, Y);
      } else {
        X = domain_removeValue(X, force(indexY));
      }
      TRACE('   - X after DIFFs:', domain__debug(X));

      ASSERT(X, 'X should be able to reflect any solution');
      if (X !== oX) setDomain(indexX, X);
    });

    bounty_markVar(bounty, indexX);
    bounty_markVar(bounty, indexY);
    somethingChanged();
    return true;
  }

  function trick_xor_elimination(xorOffset, indexX, countsX, indexY) {
    // the xor is basically a diff (!=) in a booly sense. so we can invert all the affected ops by inverting the xor.
    // bascially we "invert" a xor by aliasing one arg to the other arg and then inverting all ops that relate to it

    // all targeted ops should only have 2 args

    // X | A, X ^ Y     ->    Y <= A
    // X !& A, X ^ Y    ->    A <= Y
    // A -> X, X ^ Y    ->    A !& Y
    // X -> A, X ^ Y    ->    A | Y

    // note: eligible LTEs must be morphed to an implication first
    // A <= X, X ^ Y    ->    A !& Y
    // X <= A, X ^ Y    ->    A | Y

    TRACE('trick_xor_elimination');
    TRACE(' - index:', indexX, '^', indexY);
    TRACE(' - domains:', domain__debug(getDomain(indexX)), '^', domain__debug(getDomain(indexY)));
    TRACE(' - meta:', bounty__debugMeta(bounty, indexX), '^', bounty__debugMeta(bounty, indexY));
    TRACE(' - verying; looking for a XOR, `X ^ Y` and then we can morph any of these;');
    //TRACE('   - LTE_LHS:   X ^ Y, X <= A     =>    A | Y');
    //TRACE('   - LTE_RHS:   X ^ Y, A <= X     =>    A !& Y');
    TRACE('   - SOME:      X ^ Y, X | A      =>    Y <= A    =>    Y -> A');
    TRACE('   - NALL:      X ^ Y, X !& A     =>    A <= Y    =>    A -> Y');
    TRACE('   - IMP_LHS:   X ^ Y, X -> A     =>    Y | A');
    TRACE('   - IMP_RHS:   X ^ Y, A -> X     =>    A !& Y');
    TRACE(' - all args must be booly pairs, or bounty-booly without LTE');

    ASSERT(countsX < BOUNTY_MAX_OFFSETS_TO_TRACK, 'this was already checked in cut_xor');
    ASSERT(ml_dec16(ml, xorOffset + 1) === 2, 'XORs only have two args');

    if (!domain_isBooly(getDomain(indexX))) {
      TRACE(' - X is non-bool, bailing');
      return false;
    }

    // we need the offsets to eliminate them and to get the "other" var index for each
    // first we need to validate.
    // - we can only have one XOR
    // - all ops must have 2 args
    // - the "other" arg must also be a booly-pair or bounty-booly
    let someOffsets = [];
    let nallOffsets = [];
    let seenXor = false;
    let impLhsOffsets = [];
    let impRhsOffsets = [];
    for (let i = 0; i < countsX; ++i) {
      let offset = bounty_getOffset(bounty, indexX, i);
      ASSERT(offset, 'the offset should exist...', offset);

      let op = ml_dec8(ml, offset);

      ASSERT(op === ML_XOR || op === ML_SOME || op === ML_NALL || op === ML_IMP, 'should be one of these four ops, bounty said so', ml__opName(op));

      if (ml_dec16(ml, offset + 1) !== 2) {
        TRACE(' - op', ml__opName(op), 'does not have 2 args (', ml_dec16(ml, offset + 1), '), bailing');
        return false;
      }

      let indexA = readIndex(ml, offset + OFFSET_C_A);
      let indexB = readIndex(ml, offset + OFFSET_C_B);
      ASSERT(indexA === indexX || indexB === indexX, 'bounty should only track ops that use target var');

      TRACE('    - current offset:', offset, ', op:', ml__opName(op), 'indexes:', indexA, indexB, ', domains:', domain__debug(getDomain(indexA, true)), domain__debug(getDomain(indexB, true)));

      // get pair
      let indexT = indexA === indexX ? indexB : indexA;

      if (bounty_getCounts(bounty, indexT) === 0) {
        TRACE(' - an arg was marked (counts=0), bailing (we will get this in the rebound)');
        // note: while there may be other ops that could be converted, we'll
        // get at least one more cutter pass and we'll eventually retry this
        return false;
      }

      let T = getDomain(indexT, true);
      if (!domain_isBoolyPair(T) && hasFlags(bounty_getMeta(bounty, indexT), BOUNTY_FLAG_NOT_BOOLY)) {
        TRACE(' - found an "other" var that was marked not booly in its meta and not a booly pair, bailing');
        return false;
      }

      if (op === ML_IMP) {
        if (indexA === indexX) {
          if (impLhsOffsets.indexOf(offset) < 0) impLhsOffsets.push(offset);
        } else {
          if (impRhsOffsets.indexOf(offset) < 0) impRhsOffsets.push(offset);
        }
      } else if (op === ML_XOR) {
        if (xorOffset !== offset) {
          TRACE(' - found a different XOR, this trick only works on one, bailing');
          return false;
        }
        seenXor = true;
      } else if (op === ML_SOME) {
        if (ml_dec16(ml, offset + 1) !== 2) {
          TRACE(' - There was a SOME that did not have 2 args, bailing');
        }
        if (someOffsets.indexOf(offset) < 0) someOffsets.push(offset);
      } else {
        ASSERT(op === ML_NALL, 'see assert above');
        if (nallOffsets.indexOf(offset) < 0) nallOffsets.push(offset);
      }
    }

    TRACE(' - collection complete; indexY =', indexY, ', XOR offset =', xorOffset, ', SOME offsets:', someOffsets, ', NALL offsets:', nallOffsets, ', IMP_LHS offsets:', impLhsOffsets, ', IMP_RHS offsets:', impRhsOffsets);

    ASSERT(seenXor, 'should have seen a XOR, bounty said there would be one');

    // okay. pattern matches. do the rewrite

    TRACE(' - pattern confirmed, morphing ops, removing XOR');
    //TRACE('   - X ^ Y, X <= A     =>    A | Y');
    //TRACE('   - X ^ Y, A <= X     =>    A !& Y');
    TRACE('   - X ^ Y, X | A      =>    Y -> A; offsets:', someOffsets);
    TRACE('   - X ^ Y, X !& A     =>    A -> Y; offsets:', nallOffsets);
    TRACE('   - X ^ Y, X -> A     =>    Y | A; offsets:', impLhsOffsets);
    TRACE('   - X ^ Y, A -> X     =>    A !& Y; offsets:', impRhsOffsets);

    TRACE_MORPH('X ^ Y, inverting LTE, SOME, NALL, IMP', '');

    TRACE(' - processing', someOffsets.length, 'SOME ops');
    for (let i = 0, len = someOffsets.length; i < len; ++i) {
      // X | A, X != Y    ->    Y <= A
      let offset = someOffsets[i];
      let index = readIndex(ml, offset + OFFSET_C_A);
      if (index === indexX) index = readIndex(ml, offset + OFFSET_C_B);
      bounty_markVar(bounty, index);
      ASSERT(ml_dec8(ml, offset) === ML_SOME, 'right?');
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, offset, 2, ML_IMP, indexY, index);
    }

    TRACE(' - processing', nallOffsets.length, 'NALL ops');
    for (let i = 0, len = nallOffsets.length; i < len; ++i) {
      // X !& A, X != Y    ->    A <= Y
      let offset = nallOffsets[i];
      let index = readIndex(ml, offset + OFFSET_C_A);
      if (index === indexX) index = readIndex(ml, offset + OFFSET_C_B);
      bounty_markVar(bounty, index);
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, offset, 2, ML_IMP, index, indexY);
    }

    TRACE(' - processing', impLhsOffsets.length, 'IMP_LHS ops');
    for (let i = 0, len = impLhsOffsets.length; i < len; ++i) {
      // X -> A, X != Y    ->    A | Y
      let offset = impLhsOffsets[i];
      let index = readIndex(ml, offset + OFFSET_C_A);
      if (index === indexX) index = readIndex(ml, offset + OFFSET_C_B);
      bounty_markVar(bounty, index);
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, offset, 2, ML_SOME, index, indexY);
    }

    TRACE(' - processing', impRhsOffsets.length, 'IMP_RHS ops');
    for (let i = 0, len = impRhsOffsets.length; i < len; ++i) {
      // X -> A, X != Y    ->    A | Y
      let offset = impRhsOffsets[i];
      let index = readIndex(ml, offset + OFFSET_C_A);
      if (index === indexX) index = readIndex(ml, offset + OFFSET_C_B);
      bounty_markVar(bounty, index);
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'should be explicitly checked above');
      ml_c2c2(ml, offset, 2, ML_NALL, index, indexY);
    }

    TRACE(' - and finally removing the XOR');
    ASSERT(ml_dec16(ml, xorOffset + 1) === 2, 'diff should have 2 args here');
    ml_eliminate(ml, xorOffset, SIZEOF_C_2);

    TRACE(' - X is a leaf constraint, defer it', indexX);
    leafs.push(indexX);
    solveStack.push((_, force, getDomain, setDomain) => {
      let X = getDomain(indexX);
      TRACE(' - xor + ops...;', indexX, '^', indexY, '  ->  ', domain__debug(X), '^', domain__debug(getDomain(indexY)));

      if (force(indexY) === 0) {
        X = domain_removeValue(X, 0);
      } else {
        X = domain_removeGtUnsafe(X, 0);
      }

      ASSERT(X, 'X should be able to reflect any solution');
      setDomain(indexX, X);
    });

    bounty_markVar(bounty, indexX);
    bounty_markVar(bounty, indexY);
    somethingChanged();
    return true;
  }

  function trick_diff_xor(ml, diffOffset, indexX, countsX, indexA) {
    TRACE('trick_diff_xor');
    TRACE(' - X != A, X ^ B    =>    X!=A,A==B');

    // find the xor. X may a counts > 2
    let xorOffset = 0;
    for (let i = 0; i < countsX; ++i) {
      let offset = bounty_getOffset(bounty, indexX, i);
      if (ml_dec8(ml, offset) === ML_XOR) {
        xorOffset = offset;
      }
    }
    ASSERT(xorOffset, 'bounty said there was at least one xor', xorOffset);

    if (ml_dec16(ml, xorOffset + 1) !== 2) {
      TRACE(' - the XOR did not have 2 args, bailing');
      return false;
    }

    ASSERT(readIndex(ml, xorOffset + OFFSET_C_A) === indexX || readIndex(ml, xorOffset + OFFSET_C_B) === indexX, 'X should be part of XOR');
    let indexB = readIndex(ml, xorOffset + OFFSET_C_A);
    if (indexB === indexX) indexB = readIndex(ml, xorOffset + OFFSET_C_B);

    let A = getDomain(indexA, true);
    let B = getDomain(indexB, true);
    let X = getDomain(indexX, true);

    TRACE(' - indexes:', indexX, '!=', indexA, ',', indexX, '^', indexB);
    TRACE(' - domains:', domain__debug(X), '!=', domain__debug(A), ',', domain__debug(X), '^', domain__debug(B));

    if (!domain_isBoolyPair(A) || !domain_isBoolyPair(B) || domain_intersection(X, A) !== A || domain_intersection(X, B) !== B) {
      // note: this implicitly tested whether A is a booly
      TRACE(' - A or B wasnt a boolypair or A did not contain all values, bailing');
      return false;
    }

    TRACE(' - pattern confirmed');
    TRACE_MORPH('X != A, X ^ B', 'X ^ A, A == B');

    ml_eliminate(ml, diffOffset, SIZEOF_C_2);

    cutAddPseudoBoolyAlias(indexB, indexA);
    somethingChanged();

    return true;
  }

  function trick_diff_alias(indexX, indexY, countsX) {
    TRACE('trick_diff_alias; index X:', indexX, ', index Y:', indexY, ', counts:', countsX);
    TRACE(' - X!=A,X!=B, size(A)==2,min(A)==min(B),max(A)==max(B)   =>   A==B');

    let X = getDomain(indexX);
    let Y = getDomain(indexY);
    TRACE(' - domains:', domain__debug(X), domain__debug(Y), '(trick only works if these are equal and size=2)');
    if (X === Y && domain_size(X) === 2) {
      // if we can find another diff on X where the domain is also equal to X, we can alias Y to that var

      for (let i = 0; i < countsX; ++i) {
        let offset = bounty_getOffset(bounty, indexX, i);
        ASSERT(offset, 'the offset should exist...', offset);

        let op = ml_dec8(ml, offset);
        TRACE('   - checking offset=', offset, 'op=', op, op === ML_DIFF);
        if (op === ML_DIFF) {
          let count = ml_dec16(ml, offset + 1);
          TRACE('     - is diff with', count, 'indexes');
          if (count !== 2) {
            TRACE('       - count must be 2 for this to work, moving to next op');
            continue;
          }

          let indexA = readIndex(ml, offset + OFFSET_C_A);
          let indexB = readIndex(ml, offset + OFFSET_C_B);
          TRACE(' - indexes:', indexA, indexB, ', domains:', domain__debug(getDomain(indexA)), domain__debug(getDomain(indexB)));
          ASSERT(indexA === indexX || indexB === indexX, 'xor should have X as either arg because bounty said so');
          let indexZ;
          if (indexA === indexX) {
            if (indexB === indexY) continue;
            indexZ = indexB;
          } else {
            ASSERT(indexB === indexX, 'x should match at least one side');
            if (indexA === indexY) continue;
            indexZ = indexA;
          }
          TRACE('     - not original diff, Z=', indexZ);

          ASSERT(indexY !== indexZ, 'deduper should have eliminated duplicate diffs');

          let Z = getDomain(indexZ);
          if (X === Z) {
            TRACE('     - domains are equal so X!=Y, X!=Z, with X==Y==Z, with size(X)=2, so Y=Z, index', indexY, '=', indexZ);
            TRACE('     - eliminating this diff, aliasing Z to Y');

            ASSERT(Y === Z);
            ASSERT(domain_size(Z) === 2);

            // no solve stack required, indexY == indexZ
            addAlias(indexZ, indexY, 'double bin diff');
            ml_eliminate(ml, offset, SIZEOF_C_2);

            bounty_markVar(bounty, indexX);
            bounty_markVar(bounty, indexY);
            bounty_markVar(bounty, indexZ);
            somethingChanged();
            return true;
          }
        }
      }
    }
    TRACE(' - unable to apply trick_diff_alias, bailing');
    return false;
  }

  function trick_xor_alias(indexX, indexY, countsX, Y, sizeY, YisBooly) {
    TRACE('trick_xor_alias; index X:', indexX, ', index Y:', indexY, ', counts:', countsX, ', sizeY:', sizeY);
    ASSERT(indexX !== indexY, 'X^Y is falsum and shouldnt occur here');

    // we are looking for `X^Y,X^B` and if `size(A)==2,dA==dB` or B is a booly then we alias them

    let YisPair = sizeY === 2;

    TRACE(' - domains:', domain__debug(getDomain(indexX)), domain__debug(Y), 'Y is booly var?', YisBooly, ', Y size?', sizeY);
    if (!YisBooly && !YisPair) {
      TRACE(' - Y is neither a booly var nor a pair so cant apply this trick; bailing');
      return false;
    }

    // we now search for any xor that uses x but not y as z
    // the first z to match YisBooly or domain y==z will be aliased
    for (let i = 0; i < countsX; ++i) {
      let offset = bounty_getOffset(bounty, indexX, i);
      ASSERT(offset, 'the offset should exist...', offset);

      let op = ml_dec8(ml, offset);
      TRACE('   - checking offset=', offset, 'op=', op, op === ML_XOR);
      if (op === ML_XOR) {
        let indexA = readIndex(ml, offset + OFFSET_C_A);
        let indexB = readIndex(ml, offset + OFFSET_C_B);
        TRACE('     - is xor, indexes:', indexA, indexB, 'confirming its not the input X and Y', indexX, indexY, '( -> it', ((indexX === indexA && indexY === indexB) || (indexX === indexB && indexY === indexA)) ? 'is' : 'isnt', ')');
        ASSERT(indexA === indexX || indexB === indexX, 'at least one argument should match X since it is X-es bounty');

        let indexZ;
        if (indexA === indexX) {
          if (indexB === indexY) continue;
          indexZ = indexB;
        } else if (indexB === indexX) {
          if (indexA === indexY) continue;
          indexZ = indexA;
        } else {
          THROW('X should be left or right of its xors');
        }

        ASSERT(indexY !== indexZ, 'deduper should have eliminated duplicate xors', indexX, indexY, indexA, indexB);

        let aliased = false;
        let Z = getDomain(indexZ, true);
        if (YisPair && Z === Y) {
          TRACE(' - true aliases. X^Y X^Z, ' + indexX + '^' + indexY + ' ' + indexX + '^' + indexZ + ', aliasing', indexZ, 'to', indexY);
          // keep the current xor (X^Y) and drop the found xor (X^Z)
          addAlias(indexZ, indexY);
          aliased = true;
        } else if (YisPair && domain_size(Z) === 2) {
          TRACE(' - pseudo aliases. X^Y X^Z, ' + indexX + '^' + indexY + ' ' + indexX + '^' + indexZ + ', aliasing', indexZ, 'to', indexY);
          TRACE(' - since Y and Z can only be "zero or nonzero", the xor forces them to pick either the zero or nonzero value, regardless of anything else');
          // keep the current xor (X^Y) and drop the found xor (X^Z)
          cutAddPseudoBoolyAlias(indexY, indexZ);
          aliased = true;
        } else if (YisBooly) {
          let metaZ = getMeta(bounty, indexZ, true); // keep booly flag
          TRACE(' - Z isnt a pair, checking meta for booly:', bounty__debugMeta(bounty, indexZ));
          if (!hasFlags(metaZ, BOUNTY_FLAG_NOT_BOOLY)) {
            TRACE(' - Y and Z are both booly and xor on the same variable. so this is a pseudo alias. slash the found xor.');
            // keep the current xor (X^Y) and drop the found xor (X^Z)
            cutAddPseudoBoolyAlias(indexY, indexZ);
            aliased = true;
          }
        }
        if (aliased) {
          TRACE(' - Y was aliased to Z, eliminating this xor and returning');
          ml_eliminate(ml, offset, SIZEOF_C_2);
          bounty_markVar(bounty, indexX);
          bounty_markVar(bounty, indexY); // the alias will mess up Y counts
          bounty_markVar(bounty, indexZ);
          somethingChanged();
          return true;
        }

        TRACE(' - Z did not match. moving to next constraint');
      }
    }
    TRACE('  - did not find a second xor; bailing');
    return false;
  }

  function trick_isall_xor(indexA, indexB, xorOffset, countsA, countsB) {
    TRACE('trick_isall_xor; index A:', indexA, ', index B:', indexB, ', counts:', countsA, countsB);
    ASSERT(countsA === 2, 'check function if this changes', countsA, countsB);

    // R^A, R=all?(X Y Z)  ->   A=nall(X Y Z)
    // the xor kind of acts like a diff in this case so we flip the isall to become a isnall on xor's other arg
    // we defer R to be xor A in the solvestack

    TRACE(' - first searching for isall op');
    for (let i = 0; i < countsA; ++i) {
      let offset = bounty_getOffset(bounty, indexA, i);
      ASSERT(offset, 'there should be as many offsets as counts unless that exceeds the max and that has been checked already');
      if (offset !== xorOffset) {
        let opcode = ml_dec8(ml, offset);
        if (opcode === ML_ISALL) {
          TRACE(' - found isall at', offset);
          return _trick_isall_xor(indexA, indexB, xorOffset, offset);
        }
      }
    }

    THROW('bounty should have asserted that an isall existed');
  }
  function _trick_isall_xor(indexR, indexB, xorOffset, isallOffset) {
    TRACE_MORPH('R^S, R=all?(X Y Z ...)', 'S=nall(X Y Z ...)');
    TRACE(' - _trick_isall_xor: now applying morph to isall and eliminating the xor');
    // note: R only has 2 counts

    let isallArgCount = ml_dec16(ml, isallOffset + 1);
    ASSERT(getAlias(ml_dec16(ml, isallOffset + SIZEOF_C + isallArgCount * 2)) === indexR);

    // morph the isall to an isnall (simply change the op) on B. dont forget to mark all its args
    ml_enc8(ml, isallOffset, ML_ISNALL);
    ml_enc16(ml, isallOffset + SIZEOF_C + isallArgCount * 2, indexB);
    ml_eliminate(ml, xorOffset, SIZEOF_C_2);

    // A of xor is R of isall. defer resolving the xor because B of xor
    // is going to be the new R of the isall-flipped-to-isnall

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - _trick_isall_xor');

      let R = getDomain(indexR);
      let B = getDomain(indexB);
      TRACE(' -', domain__debug(R), '^', domain__debug(B));

      // since S is solved according to "not isall", we only have to force R^S here
      // (we didnt eliminate the isall, we just transformed it)

      ASSERT(domain_isBooly(R));
      if (domain_isBooly(B)) B = domain_createValue(force(indexB));
      if (domain_isZero(B)) {
        R = domain_removeValue(R, 0);
      } else {
        ASSERT(domain_hasNoZero(B));
        R = domain_removeGtUnsafe(R, 0);
      }
      setDomain(indexR, R);

      ASSERT(getDomain(indexR));
      ASSERT(getDomain(indexB));
      ASSERT(!domain_isBooly(getDomain(indexR)) && !domain_isBooly(getDomain(indexB)));
      ASSERT(domain_isZero(getDomain(indexR)) !== domain_isZero(getDomain(indexB)));
    });

    bounty_markVar(bounty, indexR); // R
    bounty_markVar(bounty, indexB);
    markAllArgs(ml, isallOffset, isallArgCount);
    somethingChanged();

    return true;
  }

  function trick_issome_xor(indexA, indexR, xorOffset, countsA, countsB) {
    TRACE('trick_issome_xor; index A:', indexA, ', index R:', indexR, ', counts:', countsA, countsB);
    TRACE(' - A^R, R=all?(X Y Z)  ->   A=nall(X Y Z)');

    // the xor kind of acts like a diff in this case so we flip the isall to become a isnone
    // and use A as the new result var for that isnone

    TRACE(' - first searching for issome op');

    for (let i = 0; i < countsA; ++i) {
      let offset = bounty_getOffset(bounty, indexA, i);
      if (offset !== xorOffset) {
        let opcode = ml_dec8(ml, offset);
        if (opcode === ML_ISSOME) {
          TRACE(' - found issome at', offset);
          return _trick_issome_xor(indexA, indexR, xorOffset, offset);
        }
      }
    }

    THROW('bounty should have asserted that an issome existed');
  }
  function _trick_issome_xor(indexR, indexA, xorOffset, issomeOffset) {
    TRACE(' - _trick_issome_xor: now applying morph to issome and eliminating the xor');
    TRACE_MORPH('A^R, R=all?(X Y Z)', 'A=nall(X Y Z)');

    let issomeArgCount = ml_dec16(ml, issomeOffset + 1);
    let issomeResultOffset = issomeOffset + SIZEOF_C + issomeArgCount * 2;

    ASSERT(indexR === readIndex(ml, issomeResultOffset), 'asserted before');

    let issomeArgs = markAndCollectArgs(ml, issomeOffset, issomeArgCount);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexR);

    // morph the issome to an isnone (simply change the op). dont forget to mark all its args
    ml_enc8(ml, issomeOffset, ML_ISNONE);
    ml_enc16(ml, issomeResultOffset, indexA);
    ml_eliminate(ml, xorOffset, SIZEOF_C_2);

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - trick_issome_xor');
      let A = getDomain(indexA);
      let R = getDomain(indexR);
      TRACE(' -', domain__debug(A), '^', domain__debug(R));
      if (domain_isZero(A)) {
        TRACE(' - A=0 so R must >0');
        R = domain_removeValue(R, 0);
        setDomain(indexR, R);
      } else if (domain_isZero(R)) {
        TRACE(' - R=0 so A must >0');
        A = domain_removeGtUnsafe(A, 0);
        setDomain(indexA, A);
      } else if (domain_hasNoZero(A)) {
        TRACE(' - A>0 so R must =0');
        R = domain_removeGtUnsafe(R, 0);
        setDomain(indexR, R);
      } else if (domain_hasNoZero(R)) {
        TRACE(' - R>0 so A must =0');
        A = domain_removeGtUnsafe(A, 0);
        setDomain(indexA, A);
      } else {
        ASSERT(domain_isBooly(A) && domain_isBooly(R));

        let allNone = true;
        let some = false;
        let boolyIndex = -1;
        for (let i = 0; i < issomeArgs.lenght; ++i) {
          let index = issomeArgs[i];
          let D = getDomain(index);
          if (domain_hasNoZero(D)) {
            some = true;
            break;
          } else if (!domain_isZero(D)) {
            allNone = false;
            boolyIndex = i;
          }
        }

        if (some) {
          TRACE(' - found at least one arg that was nonzero, R>0');
          R = domain_removeValue(R, 0);
        } else if (allNone) {
          TRACE(' - all args were zero, R=0');
          R = domain_removeGtUnsafe(R, 0);
        } else {
          TRACE(' - found no nonzero and at least one arg was booly, forcing R>0 and that arg >0 as well');
          R = domain_removeValue(R, 0);
          let index = issomeArgs[boolyIndex];
          let D = getDomain(index);
          ASSERT(domain_isBooly(D), 'we. just. checked. this');
          D = domain_removeValue(D, 0);
          ASSERT(D);
          setDomain(index, D);
        }
        setDomain(indexR, R);
      }

      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexR));
      ASSERT(!domain_isBooly(getDomain(indexA)) && !domain_isBooly(getDomain(indexR)));
      ASSERT(domain_isZero(getDomain(indexA)) !== domain_isZero(getDomain(indexR)));
      ASSERT(domain_hasNoZero(getDomain(indexR)) === issomeArgs.some(i => domain_hasNoZero(getDomain(i))));
    });

    somethingChanged();

    return true;
  }

  function trick_some_xor(indexX, indexA, xorOffset, countsX) {
    TRACE('trick_some_xor; X^A,X|B => A->B, X leaf');

    let offset1 = bounty_getOffset(bounty, indexX, 0);
    let offset2 = bounty_getOffset(bounty, indexX, 1);
    let someOffset = offset1 === xorOffset ? offset2 : offset1;
    TRACE(' - xorOffset:', xorOffset, ', someOffset:', someOffset, ', indexX:', indexX, ', metaX:', bounty__debugMeta(bounty, indexA));

    ASSERT(ml_dec16(ml, xorOffset + 1) === 2, 'xors have 2 args');
    ASSERT(countsX === 2, 'x should be part of SOME and XOR');

    if (ml_dec16(ml, someOffset + 1) !== 2) {
      TRACE(' - SOME doesnt have 2 args, bailing');
      return false;
    }

    let X = getDomain(indexX, true);
    if (!domain_isBooly(X)) {
      TRACE(' - X is not a booly, this should be solved by minimizer, bailing');
      requestAnotherCycle = true;
      return false;
    }

    ASSERT(readIndex(ml, someOffset + OFFSET_C_A) === indexX || readIndex(ml, someOffset + OFFSET_C_B) === indexX);
    let indexB = readIndex(ml, someOffset + OFFSET_C_A);
    if (indexB === indexX) indexB = readIndex(ml, someOffset + OFFSET_C_B);

    TRACE(' - indexes: X=', indexX, ', A=', indexA, ', B=', indexB);
    TRACE(' - domains: X=', domain__debug(getDomain(indexX)), ', A=', domain__debug(getDomain(indexA)), ', B=', domain__debug(getDomain(indexB)));

    TRACE_MORPH('X ^ A, X | B', 'A -> B');
    TRACE(' - indexes: A=', indexA, ', B=', indexB, ', X=', indexX);
    TRACE(' - domains: A=', domain__debug(getDomain(indexA)), ', B=', domain__debug(getDomain(indexB)), ', X=', domain__debug(getDomain(indexX)));

    // we dont have to bother with booly checks since there are two occurrences of X left and they both concern booly ops

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE('trick_some_xor');

      let A = getDomain(indexA);
      let B = getDomain(indexB);
      let X = getDomain(indexX);
      TRACE(' - X ^ A, X | B  =>  A -> B');
      TRACE(' - A=', domain__debug(A), ', B=', domain__debug(B), ', X=', domain__debug(X));

      if (domain_isZero(A)) {
        TRACE(' - A=0 so X>0');
        X = domain_removeValue(X, 0);
      } else if (domain_hasNoZero(A)) {
        TRACE(' - A>0 so X=0');
        X = domain_removeGtUnsafe(X, 0);
      } else if (domain_isZero(B)) {
        TRACE(' - B=0 so X>0');
        X = domain_removeValue(X, 0);
      } else {
        TRACE(' - A is booly and B>0 so force A and solve X accordingly');
        if (force(indexA) === 0) {
          TRACE(' - A=0 so X>0');
          X = domain_removeValue(X, 0);
        } else {
          TRACE(' - A>0 so X=0');
          X = domain_removeGtUnsafe(X, 0);
        }
      }

      setDomain(indexX, X);

      ASSERT(getDomain(indexA) && !domain_isBooly(getDomain(indexA)));
      ASSERT(getDomain(indexB));
      ASSERT(getDomain(indexX) && !domain_isBooly(getDomain(indexX)));
      ASSERT(domain_isZero(getDomain(indexA)) !== domain_isZero(getDomain(indexX)));
      ASSERT(!domain_hasZero(getDomain(indexX)) || !domain_hasZero(getDomain(indexB)));
    });

    ml_eliminate(ml, someOffset, SIZEOF_C_2);
    ml_c2c2(ml, xorOffset, 2, ML_IMP, indexA, indexB);

    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexX);
    somethingChanged();
    return true;
  }

  function trickNallOnly(indexX, countsX) {
    TRACE('trickNallOnly;', indexX, ', counts:', countsX);

    if (countsX >= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      TRACE(' - counts (', countsX, ') is higher than max number of offsets we track so we bail on this trick');
      return false;
    }

    let X = getDomain(indexX, true);
    if (domain_isZero(X)) {
      TRACE(' - X has is zero so NALL is already solved, rerouting to minimizer');
      requestAnotherCycle = true;
      return false;
    }
    if (domain_hasNoZero(X)) {
      TRACE(' - X has has no zero should be removed from NALL, rerouting to minimizer');
      requestAnotherCycle = true;
      return false;
    }

    TRACE(' - X contains zero and is only part of nalls, leaf X and eliminate the nalls');

    let offsets = []; // to eliminate
    let indexes = []; // to mark and to defer solve
    for (let i = 0; i < countsX; ++i) {
      let offset = bounty_getOffset(bounty, indexX, i);
      ASSERT(offset, 'bounty should assert that there are counts offsets');
      ASSERT(ml_dec8(ml, offset) === ML_NALL, 'bounty should assert that all ops are nalls');

      let argCount = ml_dec16(ml, offset + 1);
      for (let j = 0; j < argCount; ++j) {
        let index = readIndex(ml, offset + SIZEOF_C + j * 2);
        if (index !== indexX) indexes.push(index);
        // dont mark here because that may affect the getOffset call above
      }
      // let's hope this list doenst grow too much... (but we have to dedupe the indexes!)
      if (offsets.indexOf(offset) < 0) offsets.push(offset);
    }
    TRACE(' - collected offsets and vars:', offsets, indexes);

    // TODO: we can improve this step and prevent some force solvings
    TRACE(' - solving X to 0 now to simplify everything');
    if (!domain_isZero(X)) {
      ASSERT(domain_hasZero(X), 'checked above');
      setDomain(indexX, domain_createValue(0));
    }

    TRACE(' - now remove these nalls:', offsets);

    for (let i = 0, len = offsets.length; i < len; ++i) {
      let offset = offsets[i];
      TRACE_MORPH('nall(X...)', '', 'leaf a nall arg that is only used in nalls');
      let argCount = ml_dec16(ml, offset + 1);
      let opSize = SIZEOF_C + argCount * 2;
      TRACE('   - argcount=', argCount, ', opSize=', opSize);
      ml_eliminate(ml, offset, opSize);
    }

    for (let i = 0, len = indexes.length; i < len; ++i) {
      let indexY = indexes[i];
      bounty_markVar(bounty, indexY);
    }

    bounty_markVar(bounty, indexX);
    somethingChanged();

    return true;
  }

  function trickSomeOnly(indexX, countsX) {
    TRACE('trickSomeOnly;', indexX, ', counts:', countsX);

    if (countsX >= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      TRACE(' - counts (', countsX, ') is higher than max number of offsets we track so we bail on this trick');
      return false;
    }

    let X = getDomain(indexX, true);
    if (domain_hasNoZero(X)) {
      TRACE(' - X has no zero so SOME is already solved, rerouting to minimizer');
      requestAnotherCycle = true;
      return false;
    }
    if (domain_isZero(X)) {
      TRACE(' - X has is zero so should be removed from this SOME, rerouting to minimizer');
      requestAnotherCycle = true;
      return false;
    }

    TRACE(' - X contains a nonzero and is only part of SOMEs, leaf X and eliminate the SOMEs');

    let offsets = []; // to eliminate
    let indexes = []; // to mark and to defer solve
    for (let i = 0; i < countsX; ++i) {
      let offset = bounty_getOffset(bounty, indexX, i);
      ASSERT(offset, 'bounty should assert that there are counts offsets');
      ASSERT(ml_dec8(ml, offset) === ML_SOME, 'bounty should assert that all ops are SOMEs');

      let argCount = ml_dec16(ml, offset + 1);
      for (let j = 0; j < argCount; ++j) {
        let index = readIndex(ml, offset + SIZEOF_C + j * 2);
        if (index !== indexX) indexes.push(index);
        // dont mark here because that may affect the getOffset call above
      }
      // let's hope this list doenst grow too much... (but we have to dedupe the indexes!)
      if (offsets.indexOf(offset) < 0) offsets.push(offset);
    }
    TRACE(' - collected offsets and vars:', offsets, indexes);

    // TODO: we can improve this step and prevent some force solvings
    TRACE(' - removing 0 from X now to simplify everything');
    if (domain_hasZero(X)) {
      ASSERT(domain_isBooly(X), 'checked above');
      setDomain(indexX, X = domain_removeValue(X, 0));
    }

    TRACE(' - now remove these SOMEs:', offsets);

    for (let i = 0, len = offsets.length; i < len; ++i) {
      let offset = offsets[i];
      TRACE_MORPH('some(X...)', '', 'leaf a SOME arg that is only used in SOMEs');
      let argCount = ml_dec16(ml, offset + 1);
      let opSize = SIZEOF_C + argCount * 2;
      TRACE('   - argcount=', argCount, ', opSize=', opSize);
      ml_eliminate(ml, offset, opSize);
    }

    for (let i = 0, len = indexes.length; i < len; ++i) {
      let indexY = indexes[i];
      bounty_markVar(bounty, indexY);
    }

    bounty_markVar(bounty, indexX);
    somethingChanged();

    return true;
  }

  function trick_ltelhs_nalls_some(indexX, countsX) {
    TRACE('trick_ltelhs_nalls_some; indexX=', indexX);
    TRACE(' - A !& X, X <= B, X | C    ->     B | C, A <= C    (for any number of nall[2] ops)');
    // TOFIX: is this bool only?

    if (!domain_isBool(getDomain(indexX))) {
      TRACE(' - X wasnt bool (', domain__debug(getDomain(indexX)), '), bailing');
      return false;
    }
    if (countsX >= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      TRACE(' - counts (', countsX, ') is higher than max number of offsets we track so we bail on this trick');
      return false;
    }

    let lteOffset;
    let someOffset;
    let nallOffsets = [];

    let indexesA = [];
    let indexB;
    let indexC;

    for (let i = 0; i < countsX; ++i) {
      let offset = bounty_getOffset(bounty, indexX, i);
      if (!offset) break;

      let opCode = ml_dec8(ml, offset);
      ASSERT(opCode === ML_NALL || opCode === ML_SOME || opCode === ML_LTE, 'bounty should assert it logged one of these three ops');

      if (ml_dec16(ml, offset + 1) !== 2) {
        TRACE(' - found an op that did not have 2 args, bailing');
        return false;
      }

      let indexL = readIndex(ml, offset + OFFSET_C_A);
      let indexR = readIndex(ml, offset + OFFSET_C_B);
      ASSERT(indexX === indexL || indexX === indexR, 'bounty should assert that x is part of this op');
      let indexY = indexL === indexX ? indexR : indexL;

      if (opCode === ML_NALL) {
        nallOffsets.push(offset);
        indexesA.push(indexY);
      } else if (opCode === ML_SOME) {
        if (someOffset) {
          TRACE(' - trick only supported with one OR, bailing');
          return false;
        }
        someOffset = offset;
        indexC = indexY;
      } else {
        ASSERT(opCode === ML_LTE, 'if not the others then this');
        if (lteOffset) {
          TRACE(' - trick only supported with one LTE, bailing');
          return false;
        }
        lteOffset = offset;
        indexB = indexY;
      }
    }

    TRACE(' - collection complete; or offset:', someOffset, ', indexesA:', indexesA, ', indexB:', indexB, ', indexC:', indexC, ', indexX:', indexX, ', lte offset:', lteOffset, ', nall offsets:', nallOffsets);
    TRACE_MORPH('A !& X, X <= B, X | C', 'B | C, A <= C');
    TRACE_MORPH('A !& X, D !& X, X <= B, X | C', 'B | C, A <= C, D <= C', 'for any nall, all ops have 2 args');
    TRACE('   - every "other" arg of each nall should be <= C');

    ml_c2c2(ml, lteOffset, 2, ML_SOME, indexB, indexC);
    ml_eliminate(ml, someOffset, SIZEOF_C_2);
    for (let i = 0, len = indexesA.length; i < len; ++i) {
      let indexA = indexesA[i];
      ml_c2c2(ml, nallOffsets[i], 2, ML_LTE, indexA, indexC);
      bounty_markVar(bounty, indexA);
    }

    //let t = `
    //  ${['   - X!&A, ', indexesA.map(indexA => domain__debug(getDomain(indexX)) + ' !& ' + domain__debug(getDomain(indexA))).join(', ')]}
    //  ${['   - X<=B, ', domain__debug(getDomain(indexX)), '<=', domain__debug(getDomain(indexB))]}
    //  ${['   - X|C,  ', domain__debug(getDomain(indexX)), '|', domain__debug(getDomain(indexC))]}
    //`;

    TRACE('   - X is a leaf var', indexX);
    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - or+lte+nalls;', indexX);
      TRACE(' - this was `A !& X, X <= B, X | C` with any number of !&');
      TRACE('   - A=', indexesA.map(index => domain__debug(getDomain(index))), ', B=', domain__debug(getDomain(indexB)), ', C=', domain__debug(getDomain(indexC)), ', X=', domain__debug(getDomain(indexX)));
      //TRACE(t)
      TRACE(' - before:');
      TRACE('   - X!&A, ', indexesA.map(indexA => domain__debug(getDomain(indexX)) + ' !& ' + domain__debug(getDomain(indexA))).join(', '));
      TRACE('   - X<=B, ', domain__debug(getDomain(indexX)), '<=', domain__debug(getDomain(indexB)));
      TRACE('   - X|C,  ', domain__debug(getDomain(indexX)), '|', domain__debug(getDomain(indexC)));

      let B = getDomain(indexB);
      let C = getDomain(indexC);
      let X = getDomain(indexX);

      TRACE(' - first scan whether X should be set or unset');
      let setIt = false;
      let unsetIt = false;

      if (domain_isZero(C)) {
        TRACE(' - C is zero so X must be set');
        setIt = true;
      }
      indexesA.forEach(indexA => {
        let A = getDomain(indexA);
        if (domain_hasNoZero(A)) {
          TRACE(' - there was a nall arg that was set so X must be unset');
          unsetIt = true;
        }
      });

      TRACE(' - so; set?', setIt, ', unset?', unsetIt);
      ASSERT(!(setIt && unsetIt));

      if (setIt) {
        X = domain_removeValue(X, 0);
        X = domain_removeGtUnsafe(X, domain_min(B));
        TRACE(' - Set X and applied LTE: X=', domain__debug(X), ', B=', domain__debug(B));
      } else if (unsetIt) {
        X = domain_removeGtUnsafe(X, 0);
        X = domain_removeGtUnsafe(X, domain_min(B));
        TRACE(' - Unsetting X and applied LTE: X=', domain__debug(X), ', B=', domain__debug(B));
      } else {
        X = domain_removeGtUnsafe(X, domain_min(B));
        if (domain_isBooly(X)) X = domain_removeValue(X, 0);
        TRACE(' - first applied LTE and then forced a booly state; X=', domain__debug(X), ', B=', domain__debug(B));
      }
      setDomain(indexX, X);

      TRACE(' - feedback new value of X (', domain__debug(X), ')');

      // if X is zero then all the NALLs are already satisfied
      if (domain_hasNoZero(X)) {
        TRACE(' - X>0 so forcing all NALL args to be zero');
        indexesA.forEach(indexA => {
          let A = getDomain(indexA);
          A = domain_removeGtUnsafe(A, 0);
          setDomain(indexA, A);
        });
      }

      TRACE(' - Remove any value from B=', domain__debug(B), 'that is below X=', domain__debug(X), ', max(X)=', domain_max(X));
      B = domain_removeLtUnsafe(B, domain_max(X));
      setDomain(indexB, B);

      TRACE(' - if X=0 then C>0, X=', domain__debug(X), ', C=', domain__debug(C));
      if (domain_isZero(X)) {
        C = domain_removeValue(C, 0);
        setDomain(indexC, C);
      }

      TRACE(' - result:');
      TRACE('   - X!&A, ', indexesA.map(indexA => domain__debug(getDomain(indexX)) + ' !& ' + domain__debug(getDomain(indexA))).join(', '));
      TRACE('   - X<=B, ', domain__debug(getDomain(indexX)), '<=', domain__debug(getDomain(indexB)));
      TRACE('   - X|C,  ', domain__debug(getDomain(indexX)), '|', domain__debug(getDomain(indexC)));

      ASSERT(getDomain(indexB));
      ASSERT(getDomain(indexC));
      ASSERT(getDomain(indexX));
      ASSERT(!indexesA.some(indexA => !domain_isZero(getDomain(indexA)) && !domain_isZero(getDomain(indexX))));
      ASSERT(domain_max(getDomain(indexX)) <= domain_min(getDomain(indexX)));
      ASSERT(domain_hasNoZero(getDomain(indexX)) || domain_hasNoZero(getDomain(indexC)));
    });

    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexC);
    bounty_markVar(bounty, indexX);
    somethingChanged();
    return true;
  }

  function trick_implhs_nalls_some(indexX, countsX) {
    TRACE('trick_implhs_nalls_some; indexX=', indexX);
    TRACE(' - A !& X, X -> B, X | C    ->     B | C, A -> C    (for any number of nall[2] ops)');
    // TOFIX: is this bool only?

    if (countsX >= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      TRACE(' - counts (', countsX, ') is higher than max number of offsets we track so we bail on this trick');
      return false;
    }

    let impOffset;
    let someOffset;
    let nallOffsets = [];

    let indexesA = [];
    let indexB;
    let indexC;

    for (let i = 0; i < countsX; ++i) {
      let offset = bounty_getOffset(bounty, indexX, i);
      if (!offset) break;

      let opCode = ml_dec8(ml, offset);
      ASSERT(opCode === ML_NALL || opCode === ML_SOME || opCode === ML_IMP, 'bounty should assert it logged one of these three ops');

      if (ml_dec16(ml, offset + 1) !== 2) {
        TRACE(' - found an op that did not have 2 args, bailing');
        return false;
      }

      let indexL = readIndex(ml, offset + OFFSET_C_A);
      let indexR = readIndex(ml, offset + OFFSET_C_B);
      ASSERT(indexX === indexL || indexX === indexR, 'bounty should assert that x is part of this op');
      let indexY = indexL === indexX ? indexR : indexL;

      if (opCode === ML_NALL) {
        nallOffsets.push(offset);
        indexesA.push(indexY);
      } else if (opCode === ML_SOME) {
        if (someOffset) {
          TRACE(' - trick only supported with one OR, bailing');
          return false;
        }
        someOffset = offset;
        indexC = indexY;
      } else {
        ASSERT(opCode === ML_IMP, 'if not the others then this');
        if (impOffset) {
          TRACE(' - trick only supported with one IMP, bailing');
          return false;
        }
        impOffset = offset;
        indexB = indexY;
      }
    }

    TRACE(' - collection complete; or offset:', someOffset, ', indexesA:', indexesA, ', indexB:', indexB, ', indexC:', indexC, ', indexX:', indexX, ', imp offset:', impOffset, ', nall offsets:', nallOffsets);
    TRACE('   - A !& X, X -> B, X | C    ->     B | C, A -> C');
    TRACE('   - A !& X, D !& X, X -> B, X | C    ->     B | C, A -> C, D -> C');
    TRACE('   - every "other" arg of each nall should be -> C');

    ml_c2c2(ml, impOffset, 2, ML_SOME, indexB, indexC);
    ml_eliminate(ml, someOffset, SIZEOF_C_2);
    for (let i = 0, len = indexesA.length; i < len; ++i) {
      let indexA = indexesA[i];
      ml_c2c2(ml, nallOffsets[i], 2, ML_IMP, indexA, indexC);
      bounty_markVar(bounty, indexA);
    }

    TRACE('   - X is a leaf var', indexX);
    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - imp+nalls+some;', indexX);
      TRACE(' - this was `A !& X, X -> B, X | C` with any number of !&');
      TRACE(' - indexes: A=', indexesA, ', B=', indexB, ', C=', indexC, ', X=', indexX);
      TRACE(' - domains: A=', indexesA.map(a => domain__debug(getDomain(a))), ', B=', domain__debug(getDomain(indexB)), ', C=', domain__debug(getDomain(indexC)), ', X=', domain__debug(getDomain(indexX)));

      let X = getDomain(indexX);
      let nX = X;

      // A !& X for all A
      if (!domain_isZero(nX)) { // if X is 0 then the nall already passes
        for (let i = 0, len = indexesA.length; i < len; ++i) {
          let indexA = indexesA[i];
          let A = getDomain(indexA);
          if (domain_hasNoZero(A) || force(indexA) !== 0) {
            TRACE(' - at least one NALL pair had a nonzero so X must be zero');
            nX = domain_removeGtUnsafe(nX, 0);
            break; // now each nall will be fulfilled since X is zero
          }
        }
      }

      // X | C so if C is zero then X must be nonzero
      let C = getDomain(indexC);
      if (domain_isBooly(C)) {
        force(C);
        C = getDomain(indexC);
      }
      if (domain_isZero(C)) {
        TRACE(' - the SOME pair C was zero so X must be nonzero');
        nX = domain_removeValue(nX, 0);
      }

      // maintain X -> B
      let B = getDomain(indexB);
      if (domain_isBooly(B)) {
        force(B);
        B = getDomain(indexB);
      }
      if (domain_isZero(B)) {
        TRACE(' - B is zero so X must be zero');
        nX = domain_removeGtUnsafe(nX, 0);
      }

      ASSERT(nX);
      if (X !== nX) setDomain(indexX, nX);
    });

    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexC);
    bounty_markVar(bounty, indexX);
    somethingChanged();
    return true;
  }

  function trick_lteboth_nall_some(indexX, countsX) {
    TRACE('trick_lteboth_nall_some', indexX);
    TRACE(' - A <= X, B | X, C !& X, X <= D     ->     A !& C, B | D, A <= D, C <= B');
    // if we can model `A !& C, A <= D` in one constraint then we should do so but I couldn't find one
    // (when more lte's are added, that's the pattern we add for each)
    // TOFIX: is this bool only?

    // we only want exactly four ops here... and if max is set to something lower then this trick has no chance at all
    if (countsX > 4 || countsX >= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      TRACE(' - we need exactly four constraints for this trick but have', countsX, ', bailing');
      return false;
    }

    // note: bounty tracks lte_rhs and lte_lhs separate so if we have four constraints
    // here can trust bounty to assert they are all our targets, no more, no less.

    // we should have; LTE_RHS, LTE_LHS, NALL, SOME
    let lteLhsOffset;
    let lteRhsOffset;
    let someOffset;
    let nallOffset;

    let indexA;
    let indexB;
    let indexC;
    let indexD;

    for (let i = 0; i < countsX; ++i) {
      let offset = bounty_getOffset(bounty, indexX, i);
      ASSERT(offset, 'bounty should assert to fetch as many offsets as there are counts');

      let opCode = ml_dec8(ml, offset);
      ASSERT(opCode === ML_NALL || opCode === ML_SOME || opCode === ML_LTE, 'bounty should assert the op is one of these');

      // TODO: this kind of breaks on an op with 1 arg
      let indexL = readIndex(ml, offset + OFFSET_C_A);
      let indexR = readIndex(ml, offset + OFFSET_C_B);
      ASSERT(indexX === indexL || indexX === indexR, 'bounty should assert X is one of the args');
      let indexY = indexL === indexX ? indexR : indexL;

      if (opCode === ML_NALL) {
        ASSERT(!nallOffset, 'cant have a second NALL as per bounty');
        indexC = indexY;
        nallOffset = offset;
      } else if (opCode === ML_SOME) {
        ASSERT(!someOffset, 'cant have a second SOME as per bounty');
        indexB = indexY;
        someOffset = offset;
      } else {
        ASSERT(opCode === ML_LTE, 'asserted by bounty see above');

        if (indexL === indexX) { // lte_lhs
          ASSERT(!lteLhsOffset, 'cant have a second lte_lhs');
          lteLhsOffset = offset;
          indexD = indexY;
        } else { // lte_rhs
          ASSERT(indexR === indexX, 'x already asserted to be one of the op args');
          ASSERT(!lteRhsOffset, 'cant have a second lte_rhs');
          lteRhsOffset = offset;
          indexA = indexY;
        }
      }
    }

    TRACE(' - collection complete; offsets:', lteLhsOffset, lteRhsOffset, someOffset, nallOffset, ', indexes: X=', indexX, ', A=', indexA, ', B=', indexB, ', C=', indexC, ', D=', indexD);
    TRACE(' - A <= X, B | X, C !& X, X <= D     ->     A !& C, B | D, A <= D, C <= B');

    ml_c2c2(ml, lteLhsOffset, 2, ML_LTE, indexA, indexD);
    ml_c2c2(ml, lteRhsOffset, 2, ML_LTE, indexC, indexD);
    ml_c2c2(ml, someOffset, 2, ML_SOME, indexB, indexD);
    ml_c2c2(ml, nallOffset, 2, ML_NALL, indexA, indexC);

    TRACE('   - X is a leaf var', indexX);
    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - some+nall+lte_lhs+lte_rhs;', indexX);

      let X = getDomain(indexX);
      if (force(indexA) === 1) { // A<=X so if A is 1, X must also be 1
        X = domain_removeValue(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      } else if (force(indexB) === 0) { // X|B so if B is 0, X must be non-zero
        X = domain_removeValue(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      } else if (force(indexC) > 0) { // if indexA is set, X must be zero
        X = domain_removeGtUnsafe(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      } else if (force(indexD) === 0) { // X<=D, if indexD is 0, X must be zero
        X = domain_removeGtUnsafe(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      }
    });

    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexC);
    bounty_markVar(bounty, indexD);
    bounty_markVar(bounty, indexX);
    somethingChanged();
    return true;
  }

  function trick_impboth_nall_some(indexX, countsX) {
    TRACE('trick_impboth_nall_some', indexX);
    TRACE(' - A -> X, B | X, C !& X, X -> D             =>     A !& C, B | D, A -> D, C -> B');
    // we want a NALL[2], SOME[2], IMP_LHS, and one or more IMP_RHS
    // if we can model `A !& C, A -> D` in one constraint then we should do so but I couldn't find one
    // - A->(B<?C)
    // - A==(C&A&!B)
    // - B<C|!A       /       B<C|A==0
    // (when more IMPs are added, we add the same pattern for each)
    // TOFIX: is this bool only?

    if (countsX !== 4 || countsX >= BOUNTY_MAX_OFFSETS_TO_TRACK) {
      TRACE(' - we need 4 constraints for this trick but have', countsX, ', bailing');
      return false;
    }

    // note: bounty tracks imp_rhs and imp_lhs separate so if we have four constraints
    // here can trust bounty to assert they are all our targets, no more, no less.
    // TODO: what if somehow X->X ocurred here? (due to other rewrite inside cutter)

    // we should have; 1x IMP_RHS, 1x IMP_LHS, 1x NALL, 1x SOME
    let impLhsOffset;
    let impRhsOffset;
    let someOffset;
    let nallOffset;

    let indexA;
    let indexB;
    let indexC;
    let indexD;

    for (let i = 0; i < countsX; ++i) {
      let offset = bounty_getOffset(bounty, indexX, i);
      ASSERT(offset, 'bounty should assert to fetch as many offsets as there are counts');

      let opCode = ml_dec8(ml, offset);
      ASSERT(opCode === ML_NALL || opCode === ML_SOME || opCode === ML_IMP, 'bounty should assert the op is one of these');

      // TODO: this kind of breaks on an op with 1 arg
      let indexL = readIndex(ml, offset + OFFSET_C_A);
      let indexR = readIndex(ml, offset + OFFSET_C_B);
      ASSERT(indexX === indexL || indexX === indexR, 'bounty should assert X is one of the args');

      if (opCode === ML_NALL) {
        ASSERT(nallOffset === undefined, 'bounty said so');

        indexC = indexL === indexX ? indexR : indexL;
        nallOffset = offset;
      } else if (opCode === ML_SOME) {
        ASSERT(someOffset === undefined, 'bounty said so');

        indexB = indexL === indexX ? indexR : indexL;
        someOffset = offset;
      } else {
        ASSERT(opCode === ML_IMP, 'asserted by bounty see above');
        let indexY = indexL === indexX ? indexR : indexL;

        if (indexL === indexX) { // imp_lhs
          ASSERT(impLhsOffset === undefined, 'bounty said so');
          impLhsOffset = offset;
          indexD = indexY;
        } else { // imp_rhs
          ASSERT(indexR === indexX, 'x already asserted to be one of the op args');
          ASSERT(impRhsOffset === undefined, 'bounty said so');
          impRhsOffset = offset;
          indexA = indexY;
        }
      }
    }

    TRACE(' - collection complete; offsets:', impLhsOffset, impRhsOffset, someOffset, nallOffset, ', indexes: X=', indexX, ', A=', indexA, ', B=', indexB, ', C=', indexC, ', D=', indexD);
    TRACE(' - A -> X, B | X, C !& X, X -> D, X -> E     =>     A !& C, B | D, A -> D, C -> B, A -> E, C -> E');

    if (!domain_isBool(getDomain(indexA, true)) || !domain_isBool(getDomain(indexB, true)) || !domain_isBool(getDomain(indexC, true)) || !domain_isBool(getDomain(indexD, true))) {
      TRACE(' - At least one of the domains wasnt a bool, bailing for now');
      return false;
    }

    TRACE_MORPH(' - C !& X, B | X, A -> X, X -> D', ' - A !& C, B | D, A -> D, C -> B');

    ml_c2c2(ml, impLhsOffset, 2, ML_IMP, indexA, indexD);
    ml_c2c2(ml, impRhsOffset, 2, ML_IMP, indexC, indexD);
    ml_c2c2(ml, someOffset, 2, ML_SOME, indexB, indexD);
    ml_c2c2(ml, nallOffset, 2, ML_NALL, indexA, indexC);

    TRACE('   - X is a leaf var', indexX);
    leafs.push(indexX);
    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - some+nall+imp_lhs+imp_rhs;', indexX);

      // TODO: we can be less forcing here

      let X = getDomain(indexX);
      if (force(indexA) === 1) { // A->X so if A is 1, X must also be 1
        X = domain_removeValue(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      } else if (force(indexB) === 0) { // X|B so if B is 0, X must be non-zero
        X = domain_removeValue(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      } else if (force(indexC) > 0) { // X!&C so if indexA is set, X must be zero
        X = domain_removeGtUnsafe(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      } else if (force(indexD) === 0) { // X->D, if indexD is 0, X must be zero
        X = domain_removeGtUnsafe(X, 0);
        ASSERT(X, 'X should be able to reflect the solution');
        setDomain(indexX, X);
      }
    });

    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexC);
    bounty_markVar(bounty, indexD);
    bounty_markVar(bounty, indexX);
    somethingChanged();
    return true;
  }

  function trick_issame_sum(ml, sumOffset, indexR, counts, argCount, sum, min, max, constantValue, constantArgIndex, allSumArgsBoolyPairs) {
    // only if all sum args are strict bools ([0 1]), one constant excluded

    // (R = sum(A B C) & (S = R==?3)        ->    S = all?(A B C)
    // (R = sum(A B C) & (S = R==?0)        ->    S = none?(A B C)
    // (R = sum(A B C) & (S = R==?[0 1])    ->    S = nall?(A B C)
    // (R = sum(A B C) & (S = R==?[1 2])    ->    S = some?(A B C)

    // R = sum( ... ), S = R ==? count                       ->   S = all?( ... )
    // R = sum( ... ), S = R ==? 0                           ->   S = none?( ... )
    // R = sum( ... ), S = R ==? [0 0 count-1 count-1]       ->   S = nall?( ... )
    // R = sum( ... ), S = R ==? [1 1 count count]           ->   S = some?( ... )

    // R = sum([0 0 3 3], [0 0 5 5]), S = R ==? 8            ->   S = all?( ... )
    // R = sum( ... ), S = R ==? sum-max-args                ->   S = all?( ... )

    let offset1 = bounty_getOffset(bounty, indexR, 0);
    let offset2 = bounty_getOffset(bounty, indexR, 1);
    let issameOffset = offset1 === sumOffset ? offset2 : offset1;
    TRACE('trick_issame_sum; sumOffset:', sumOffset, ', issameOffset:', issameOffset, ', indexR:', indexR, ', countsR:', counts, ', metaR:', bounty__debugMeta(bounty, indexR), ', min:', min, ', max:', max, ', const:', constantValue, ', const arg pos:', constantArgIndex);

    ASSERT(min >= 0 && max >= 0 && min <= max, 'min/max check');
    ASSERT(constantValue >= 0, 'constant value should be positive or zero');
    ASSERT(issameOffset > 0, 'offset should exist and cant be the first op');
    ASSERT(counts === 2, 'R should only be used in two constraints (sum and issame)');
    ASSERT(getMeta(bounty, indexR) === (BOUNTY_FLAG_ISSAME_ARG | BOUNTY_FLAG_SUM_RESULT), 'should be sum and issame arg', counts, bounty__debugMeta(bounty, indexR));
    ASSERT(ml_dec8(ml, sumOffset) === ML_SUM, 'check sum offset');
    ASSERT(ml_dec8(ml, issameOffset) === ML_ISSAME, 'check issame offset');
    ASSERT(ml_dec16(ml, sumOffset + 1) === argCount, 'argcount should match');
    ASSERT(constantArgIndex < argCount, 'should be valid const pos');

    let issameArgCount = ml_dec16(ml, issameOffset + 1);
    if (issameArgCount !== 2) {
      TRACE(' - issame does not have 2 args, bailing for now');
      return false;
    }

    // S = R ==? X
    let indexA = readIndex(ml, issameOffset + OFFSET_C_A); // R or X
    let indexB = readIndex(ml, issameOffset + OFFSET_C_B); // R or X
    let indexS = readIndex(ml, issameOffset + OFFSET_C_R); // S

    ASSERT(indexA === indexR || indexB === indexR, 'R should be an arg of the issame');
    let indexX = indexA;
    if (indexX === indexR) indexX = indexB;

    TRACE(' - S = R ==? X; indexes=', indexS, '=', indexR, '==?', indexX);
    TRACE(' - ', domain__debug(getDomain(indexS)), '=', domain__debug(getDomain(indexR)), '==?', domain__debug(getDomain(indexX)));

    let R = getDomain(indexR, true);
    let X = getDomain(indexX, true);
    let vX = domain_getValue(X);

    if (vX >= 0 && !domain_containsValue(R, vX)) {
      // this case should be handled by the minimizer but deduper/earlier cutter steps could lead to it here anyways
      // bailing so minimizer can take care of it in the next cycle
      TRACE(' - R didnt contain B so unsafe for leaf cutting, bailing');
      requestAnotherCycle = true;
      return false;
    }

    //let want = domain_createRange(min, max);
    let Rwant = domain_intersection(R, sum);
    TRACE(' - R must contain all values in between;', domain__debug(R), 'and', domain__debug(sum), '=', domain__debug(Rwant), '(', sum === Rwant, ')');
    if (Rwant !== sum) {
      TRACE(' - R cant represent all values of the sum');//, are the args booly pairs?', allSumArgsBoolyPairs, ', vX:', vX, ', max:', max);
      return false;
    }
    TRACE(' - sum R range change check passed');

    // check the case where all the args are boolyPairs and R contains the sum of maxes
    if (allSumArgsBoolyPairs && vX === max) {
      // R = sum([0 0 3 3], [0 0 5 5]), S = R ==? 8            ->   S = all?( ... )
      // R = sum( ... ), S = R ==? sum-max-args                ->   S = all?( ... )
      TRACE(' - all sum args are booly and vX is the sum of maxes, morph to isall');
      TRACE_MORPH('R = sum( ... ), S = R ==? sum-max-args', 'S = all?( ... )');
      ml_enc8(ml, sumOffset, ML_ISALL);
      return _trick_issame_sum_tail(sumOffset, issameOffset, argCount, indexR, indexS, indexX, constantValue, constantArgIndex);
    }

    if (vX >= 0) {
      return _trick_issame_sum_constant(ml, sumOffset, argCount, indexR, issameOffset, indexS, indexX, vX, max, constantValue, constantArgIndex);
    } else {
      return _trick_issame_sum_domain(ml, sumOffset, argCount, indexR, issameOffset, indexS, indexX, X, constantValue, constantArgIndex);
    }
  }
  function _trick_issame_sum_constant(ml, sumOffset, argCount, indexR, issameOffset, indexS, indexX, vX, max, constantValue, constantArgIndex) {
    TRACE(' - _trick_issame_sum_constant', vX);
    // this is when the X of S=R==?X is a constant

    // R = sum(A B C), S = R ==? 0          "are none of ABC set"
    // R = sum(A B C 5), S = R ==? 0        S=0 because R is always at least 5. we ignore this here
    // R = sum(A B C 5), S = R ==? 5        "are none of ABC set"

    // R = sum(A B C), S = R ==? 3          "are all args set"
    // R = sum(A B C 5), S = R ==? 3        S=0 because R is always at least 5. we ignore this here
    // R = sum(A B C 5), S = R ==? 8        "are all args set"

    // note: we're not checking the sum bounds here (R is not a leaf). we only want to know how
    // the sum bounds relate to X of the issame.

    TRACE(' - vX=', vX, ', constantValue=', constantValue, ', const arg pos:', constantArgIndex, ', argCount=', argCount, ', for isnone, vX must be', constantValue, ', for isall vX must be', argCount + (constantValue ? constantValue - 1 : 0));
    ASSERT(constantArgIndex < argCount, 'const pos should be valid');
    ASSERT(ml_dec16(ml, issameOffset + 1) === 2, 'issame should have 2 args');

    // to remind you; all sum args are at least booly and there is at most one constant among them

    if (vX === constantValue) {
      // this means all non-constant args must become zero
      // for example; R=sum(A,B,C,3,8),S=R==?11 => A=B=C=0
      TRACE(' - min=X so all non-constants must be set to zero to satisfy the sum+issame. that means morph to isnone');
      TRACE_MORPH('R=sum(A,B,C,x,y),S=R==?(x+y)', 'A=B=C=0');

      // sum will fit isnone. it'll be exactly the same size
      // only need to update the op code and the result index, as the rest remains the same
      ml_enc8(ml, sumOffset, ML_ISNONE);
    } else if (vX === max) {
      // this means all non-constant args must be non-zero
      // for example: R=sum(A:[0 1],B:[0 0 2 2],C:[0 1],3,8),S=R==?15 => S=all?(A B C)
      TRACE(' - (c+a-1)==X so all non-constants must be set to non-zero to satisfy the sum+issame. that means morph to isall');
      TRACE_MORPH('R=sum(A:boolypair,B:boolypair,...,y,z,...),S=R==?(max(A)+max(B)+x+y+...)', 'S=all?(A B C ...)');

      // sum will fit isall. it'll be exactly the same size
      // only need to update the op code and the result index, as the rest remains the same
      ml_enc8(ml, sumOffset, ML_ISALL);
    } else {
      TRACE(' - min < X < max, cant morph this, bailing');
      return false;
    }

    return _trick_issame_sum_tail(sumOffset, issameOffset, argCount, indexR, indexS, indexX, constantValue, constantArgIndex);
  }
  function _trick_issame_sum_domain(ml, sumOffset, argCount, indexR, issameOffset, indexS, indexX, X, constantValue, constantArgIndex) {
    TRACE(' - _trick_issame_sum_domain', domain__debug(X));
    // this is when the X of S=R==?X is an unsolved domain

    // R = sum(A B C), S = R ==? [0 2]      "are not all of ABC set"
    // R = sum(A B C 5), S = R ==? [0 2]    S=0 because R is always at least 5. we ignore this here
    // R = sum(A B C 5), S = R ==? [5 7]    "are not all of ABC set"

    // R = sum(A B C), S = R ==? [1 3]      "are some of ABC set"
    // R = sum(A B C 5), S = R ==? [1 3]    S=0 because R is always at least 5. we ignore this here
    // R = sum(A B C 5), S = R ==? [6 8]    "are some of ABC set"

    // note: we're not checking the sum bounds here (R is not a leaf). we only want to know how
    // the sum bounds relate to X of the issame.

    TRACE(' - n=', argCount, ', c=', constantValue, '; X=', domain__debug(X), ', issome means [c+1 c+n-1] so [', constantValue + 1, ',', constantValue + argCount - 1, '], and isnall means [c (c-(C?1:0))+n-1] so [', constantValue, ',', (constantValue - (constantValue ? 1 : 0)) + (argCount - 1), ']');
    ASSERT(ml_dec16(ml, issameOffset + 1) === 2, 'issame should have 2 args');

    if (X === domain_createRange(constantValue + 1, constantValue + argCount - (constantValue ? 1 : 0))) {
      TRACE(' - X requires at least one var to be set, so issome');
      TRACE_MORPH('R = sum(A:bool B:bool C:bool), S = R ==? [1 3]', 'S = some?(A B C)');
      ml_enc8(ml, sumOffset, ML_ISSOME);
    } else if (X === domain_createRange(constantValue, (constantValue - (constantValue ? 1 : 0)) + (argCount - 1))) {
      TRACE(' - X requires one var to be unset, so isnall');
      TRACE_MORPH('R = sum(A:bool B:bool C:bool), S = R ==? [0 2]', 'S = nall?(A B C)');
      ml_enc8(ml, sumOffset, ML_ISNALL);
    } else {
      TRACE(' - sum bounds does not match X in a useful way, bailing');
      return false;
    }

    return _trick_issame_sum_tail(sumOffset, issameOffset, argCount, indexR, indexS, indexX, constantValue, constantArgIndex);
  }
  function _trick_issame_sum_tail(sumOffset, issameOffset, argCount, indexR, indexS, indexX, constantValue, constantArgIndex) {
    // note: NO bailing here
    TRACE(' - _trick_issame_sum_tail');
    ASSERT(ml_dec16(ml, issameOffset + 1) === 2, 'issame should have 2 args');
    let newArgCount = removeOneConstantFromArgs(constantValue, constantArgIndex, argCount, sumOffset);

    // make S the result var for the isnall/issome/isnone/isall
    ml_enc16(ml, sumOffset + SIZEOF_C + newArgCount * 2, indexS);

    TRACE(' - eliminating the issame, marking all affected vars');

    let args = markAndCollectArgs(ml, sumOffset, newArgCount);

    // (R = sum(A B C) & (S = R==?3)        ->    S = all?(A B C)
    // (R = sum(A B C) & (S = R==?0)        ->    S = none?(A B C)
    // (R = sum(A B C) & (S = R==?[0 1])    ->    S = nall?(A B C)
    // (R = sum(A B C) & (S = R==?[1 2])    ->    S = some?(A B C)

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - _trick_issame_sum_tail; force solving the issame (only)');
      // note: the sum is handled through addSumToSolveStack, which should resolve before this solvestack entry

      let S = getDomain(indexS);
      let R = getDomain(indexR);
      let X = getDomain(indexX);
      ASSERT(domain_isSolved(R), 'this should be solved by the solvestack compiled after this one (addSumToSolveStack)');
      TRACE(' - before: S=', domain__debug(S), ' = R=', domain__debug(R), ' ==? X=', domain__debug(X));

      if (!domain_isBooly(S)) {
        if (!domain_intersection(R, X)) {
          TRACE(' R and X dont intersect so S is falsy');
          S = domain_removeGtUnsafe(S, 0);
          setDomain(indexS, S);
        } else {
          force(indexX);
          X = getDomain(indexX);
          // note: R should be solved here
          if (R === X) {
            TRACE(' - X==R so set S to truthy');
            S = domain_removeValue(S, 0);
            setDomain(indexS, S);
          } else {
            TRACE(' - X!=R so set S to falsy');
            S = domain_removeGtUnsafe(S, 0);
            setDomain(indexS, S);
          }
        }
      }

      TRACE(' - between: S=', domain__debug(S), ' = R=', domain__debug(R), ' ==? X=', domain__debug(X));

      ASSERT(!domain_isBooly(S));
      if (domain_isZero(S)) {
        TRACE(' - S=0 so X != R');
        X = domain_removeValue(X, domain_getValue(R));
      } else {
        TRACE(' - S>0 so X == R');
        X = domain_intersection(X, R);
      }
      setDomain(indexX, X);

      TRACE(' - after: S=', domain__debug(S), ' = R=', domain__debug(R), ' ==? X=', domain__debug(X));

      ASSERT(getDomain(indexS));
      ASSERT(getDomain(indexX));
      ASSERT(getDomain(indexR), 'enforced by other solve stack');
      ASSERT(!domain_isBooly(getDomain(indexS)));
      ASSERT(domain_isSolved(getDomain(indexR)), 'the sum result should also be solved (enforced by other solve stack)');
      ASSERT(domain_isZero(getDomain(indexS)) || domain_isSolved(getDomain(indexX)), 'if S>0 then X must be solved to guarantee the eq');
      ASSERT(domain_isZero(getDomain(indexS)) === !domain_intersection(getDomain(indexR), getDomain(indexX)));
    });
    addSumToSolveStack(indexR, args, constantValue);

    ml_eliminate(ml, issameOffset, SIZEOF_CR_2);

    ASSERT(newArgCount === args.length);
    bounty_markVar(bounty, indexS);
    bounty_markVar(bounty, indexR);
    bounty_markVar(bounty, indexX);
    somethingChanged();
    return true;
  }

  function trick_islte_sum(ml, sumOffset, indexR, counts, argCount, min, max, constantValue, constantArgIndex) {
    // only if all sum args are strict bools ([0 1]), one constant excluded

    // (R = sum(A B C) & (S = R<=?0)        ->    S = none?(A B C)
    // (R = sum(A B C) & (S = R<=?2)        ->    S = nall?(A B C)
    // (R = sum(A B C) & (S = 1<=?R)        ->    S = some?(A B C)
    // (R = sum(A B C) & (S = 3<=?R)        ->    S = all?(A B C)

    // R = sum( ... ), S = R <=? 0          ->    S = none?( ... )
    // R = sum( ... ), S = R <=? count-1    ->    S = nall?( ... )
    // R = sum( ... ), S = 1 <=? R          ->    S = some?( ... )
    // R = sum( ... ), S = count <=? R      ->    S = all?( ... )

    let offset1 = bounty_getOffset(bounty, indexR, 0);
    let offset2 = bounty_getOffset(bounty, indexR, 1);
    let islteOffset = offset1 === sumOffset ? offset2 : offset1;
    TRACE('trick_islte_sum; sumOffset:', sumOffset, ', islteOffset:', islteOffset, ', indexR:', indexR, ', countsR:', counts, ', metaR:', bounty__debugMeta(bounty, indexR), ', min=', min, ', max=', max, ', constantValue=', constantValue);

    ASSERT(islteOffset > 0, 'offset should exist and cant be the first op');
    ASSERT(counts === 2, 'R should only be used in two constraints (sum and islte)');
    ASSERT(getMeta(bounty, indexR) === (BOUNTY_FLAG_ISLTE_ARG | BOUNTY_FLAG_SUM_RESULT), 'should be sum and islte arg', counts, bounty__debugMeta(bounty, indexR));
    ASSERT(ml_dec8(ml, sumOffset) === ML_SUM, 'check sum offset');
    ASSERT(ml_dec8(ml, islteOffset) === ML_ISLTE, 'check islte offset');
    ASSERT(ml_dec16(ml, sumOffset + 1) === argCount, 'argcount should match');

    let indexA = readIndex(ml, islteOffset + 1); // R or ?
    let indexB = readIndex(ml, islteOffset + 3); // R or ?
    let indexS = readIndex(ml, islteOffset + 5); // S

    ASSERT(indexA === indexR || indexB === indexR, 'R should be an arg of the islte');

    let indexX = indexA;
    if (indexX === indexR) indexX = indexB;

    // (R = sum(...) & (S = A<=?B)
    // (R = sum(...) & (S = R<=?X) or
    // (R = sum(...) & (S = X<=?R)

    let X = getDomain(indexX, true);
    let vX = domain_getValue(X);
    // we cant check 0 1 n-1 n here because a constant could affect those values. so only check whether X is solved.
    if (vX < 0) {
      TRACE(' - X is not solved, bailing');
      return false;
    }

    let R = getDomain(indexR, true);

    if (!domain_containsValue(R, vX)) {
      // this case should be handled by the minimizer but deduper/earlier cutter steps could lead to it here anyways
      // bailing so minimizer can take care of it in the next cycle
      TRACE(' - R didnt contain B so unsafe for leaf cutting, bailing');
      requestAnotherCycle = true;
      return false;
    }

    TRACE(' - validating sum args now');

    let want = domain_createRange(min, max);
    let Rwant = domain_intersection(R, want);
    TRACE(' - sum args summed; min is', min, 'and max is', max, ', R must contain all values in between;', domain__debug(R), 'and', domain__debug(want), '=', domain__debug(Rwant), '(', Rwant === want, ')');

    if (Rwant !== want) {
      TRACE(' - R cant represent all values of the sum so bailing');
      return false;
    }

    // note: we're not checking the sum bounds here (R is not a leaf). we only want to know how
    // the sum bounds relate to X of the islte.

    // the position of R in the isLte determines what values we care about here
    // R = sum( ... ), S = R <=? 0          =>    S = none?( ... )
    // R = sum( ... ), S = R <=? count-1    =>    S = nall?( ... )
    // R = sum( ... ), S = 1 <=? R          =>    S = some?( ... )
    // R = sum( ... ), S = count <=? R      =>    S = all?( ... )

    let targetOp = 0;
    if (indexA === indexR) {
      ASSERT(indexB === indexX);
      TRACE(' - X=', vX, ', n=', argCount, ', c=', constantValue, ', x is to the right. we care about 0 and n-1 (', constantValue, 'and', constantValue - (constantValue ? 1 : 0) + (argCount - 1), ')');

      // R = sum(A B C), S = R <=? 0          "are none of ABC set"
      // R = sum(A B C 5), S = R <=? 0        S=0 because R is always at least 5. we ignore this here
      // R = sum(A B C 5), S = R <=? 5        "are non of ABC set"

      // R = sum(A B C), S = R <=? 2          "are at most 2 of ABC set"
      // R = sum(A B C 5), S = R <=? 2        S=0 because R is always at least 5. we ignore this here
      // R = sum(A B C 5), S = R <=? 7        "are at most 2 of ABC set"

      if (vX === constantValue) { //
        TRACE(' - this is "are none of the sum args set, ignoring the constant"');
        TRACE_MORPH('R = sum(A B C ...), S = R <=? 0', 'S = none?(A B C ...)');
        targetOp = ML_ISNONE;
      } else if (vX === (constantValue - (constantValue ? 1 : 0) + (argCount - 1))) {
        TRACE(' - this is "are not all of the sum args set, ignoring the constant"');
        TRACE_MORPH('R = sum( ... ), S = R <=? count-1', 'S = nall?( ... )');
        targetOp = ML_ISNALL;
      } else {
        TRACE(' - Unable to apply trick, bailing');
        return false;
      }
    } else {
      ASSERT(indexA === indexX && indexB === indexR);
      TRACE(' - X=', vX, ', n=', argCount, ', c=', constantValue, ', x is to the left. we care about 1 and n (', constantValue + 1, 'and', constantValue - (constantValue ? 1 : 0) + argCount, ')');

      // R = sum(A B C), S = 1 <= R          "are some of ABC set"
      // R = sum(A B C 5), S = 1 <=? R        S=1 because R is always at least 5. we ignore this here
      // R = sum(A B C 5), S = 6 <=? R        "are some of ABC set"

      // R = sum(A B C), S = 3 <=? R          "are all of ABC set"
      // R = sum(A B C 5), S = 4 <=? R        S=1 because R is always at least 5. we ignore this here
      // R = sum(A B C 5), S = 5+4-1 <=? R    "are all of ABC set"

      if (vX === (constantValue + 1)) {
        TRACE(' - this is "is at least one sum arg set"');
        TRACE('R = sum( ... ), S = 1 <=? R', 'S = some?( ... )');
        targetOp = ML_ISSOME;
      } else if (vX === (constantValue - (constantValue ? 1 : 0) + argCount)) {
        TRACE(' - this is "are all of the sum args set"');
        TRACE('R = sum( ... ), S = count <=? R', 'S = all?( ... )');
        targetOp = ML_ISALL;
      } else {
        TRACE(' - Unable to apply trick, bailing');
        return false;
      }
    }
    ASSERT(targetOp !== 0, 'should be one of the four reifier ops');

    // NOW update the op. we won't bail after this point.
    ml_enc8(ml, sumOffset, targetOp);

    TRACE(' - eliminating the islte, marking all affected vars');
    TRACE(' - constant value:', constantValue, ', arg index:', constantArgIndex);

    let newArgCount = removeOneConstantFromArgs(constantValue, constantArgIndex, argCount, sumOffset);
    let args = markAndCollectArgs(ml, sumOffset, newArgCount);

    // the position of R in the isLte determines what values we care about here
    // R = sum( ... ), S = R <=? 0          =>    S = none?( ... )
    // R = sum( ... ), S = R <=? count-1    =>    S = nall?( ... )
    // R = sum( ... ), S = 1 <=? R          =>    S = some?( ... )
    // R = sum( ... ), S = count <=? R      =>    S = all?( ... )

    // make S the result var for the reifier
    ml_enc16(ml, sumOffset + SIZEOF_C + newArgCount * 2, indexS);

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - trick_islte_sum; force solving S (only)');
      // note: the sum is handled through addSumToSolveStack, which should resolve before this solvestack entry

      let S = getDomain(indexS);
      let R = getDomain(indexR);
      ASSERT(domain_isSolved(R), 'this should be solved by the solvestack compiled after this one (addSumToSolveStack)');
      TRACE(' - before: S=', domain__debug(S), ', R=', domain__debug(R), ', vX=', vX, ', x left?', indexA === indexX);

      if (!domain_isBooly(S)) {
        if (indexX === indexA) {
          // S = x <= R
          if (vX <= domain_min(R)) {
            TRACE(' - x<=R so set S to truthy');
            S = domain_removeValue(S, 0);
            setDomain(indexS, S);
          } else {
            TRACE(' - R>x so set S to falsy');
            S = domain_removeGtUnsafe(S, 0);
            setDomain(indexS, S);
          }
        } else {
          // S = R <= x
          if (domain_max(R) <= vX) {
            TRACE(' - R<=x so set S to truthy');
            S = domain_removeValue(S, 0);
            setDomain(indexS, S);
          } else {
            TRACE(' - R>x so set S to falsy');
            S = domain_removeGtUnsafe(S, 0);
            setDomain(indexS, S);
          }
        }
      }
      TRACE(' - after: S=', domain__debug(getDomain(indexS)), ', R=', domain__debug(getDomain(indexR)), ', X=', domain__debug(getDomain(indexX)));

      ASSERT(getDomain(indexS));
      ASSERT(getDomain(indexR), 'enforced by other solve stack');
      ASSERT(args.every(getDomain));
      ASSERT(!domain_isBooly(getDomain(indexS)));
      ASSERT(domain_isSolved(getDomain(indexR)), 'the sum result should also be solved (enforced by other solve stack)');
      ASSERT(domain_isZero(getDomain(indexS)) !== (indexX === indexA ? vX <= domain_min(getDomain(indexR)) : (domain_max(getDomain(indexR)) <= vX)), 'S=x<=R or S=R<=x should hold');
    });
    addSumToSolveStack(indexR, args, constantValue);

    ml_eliminate(ml, islteOffset, SIZEOF_VVV);

    bounty_markVar(bounty, indexR);
    somethingChanged();
    return true;
  }

  function trick_xnor_pseudoSame(ml, offset, indexA, boolyA, indexB, boolyB) {
    // A or B or both are only used as a boolean (in the zero-nonzero sense, not strictly 0,1)
    // the xnor basically says that if one is zero the other one is too, and otherwise neither is zero
    // cominbing that with the knowledge that both vars are only used for zero-nonzero, one can be
    // considered a pseudo-alias for the other. we replace it with the other var and defer solving it.
    // when possible, pick a strictly boolean domain because it's more likely to allow new tricks.

    // note that for a booly, the actual value is irrelevant. whether it's 1 or 5, the ops will normalize
    // this to zero and non-zero anyways. and by assertion the actual value is not used inside the problem

    TRACE(' - trick_xnor_pseudoSame; found booly-eq in a xnor:', indexA, '!^', indexB, ', A booly?', boolyA, ', B booly?', boolyB);
    ASSERT(boolyA || boolyB, 'at least one of the args should be a real booly (as reported by bounty)');
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'should have 2 args');

    // ok, a little tricky, but we're going to consider the bool to be a full alias of the other var.
    // once we create a solution we will override the value and apply the booly constraint and assign
    // it either its zero or nonzero value(s) depending on the other value of this xnor.

    let indexEliminate = indexB; // Eliminate
    let indexKeep = indexA; // Keep

    // keep the non-bool if possible
    if (!boolyB) {
      TRACE(' - keeping B instead because its not a booly');
      indexEliminate = indexA;
      indexKeep = indexB;
    }

    cutAddPseudoBoolyAlias(indexKeep, indexEliminate);

    ml_eliminate(ml, offset, SIZEOF_C_2);
    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    somethingChanged();
  }

  function trick_sum_booly(ml, sumOffset, indexR, countsR, sum, argCount) {
    // R is used as a result var for a sum
    // we must first confirm that R is a booly (only used as arg in booly places of ops), except for being a sum-result
    // in that case the sum is an isSome because that's the only thing that matters for R
    // note that the meta flags will claim non-booly because (at least) R is the sum result var so we gotta confirm that

    TRACE('trick_sum_booly; sumOffset:', sumOffset, ', indexR:', indexR, ', countsR:', countsR, ', argCount:', argCount, ', metaR:', bounty__debugMeta(bounty, indexR));

    ASSERT((getMeta(bounty, indexR) & BOUNTY_FLAG_SUM_RESULT) === BOUNTY_FLAG_SUM_RESULT, 'shouldve been confirmed');
    ASSERT(ml_dec16(ml, sumOffset + 1) === argCount, 'argcount should match');

    let R = getDomain(indexR, true);
    TRACE(' - first checking whether R (', domain__debug(R), ') is a booly when not counting this sum (pair?', domain_isBoolyPair(R), ')');

    if (!domain_isBoolyPair(R)) { // if a var only has a zero and one nonzero value it doesnt matter: it's always booly
      for (let i = 0; i < countsR; ++i) {
        let offset = bounty_getOffset(bounty, indexR, i);
        ASSERT(offset, 'should exist');

        if (offset !== sumOffset) {
          let opCode = ml_dec8(ml, offset);
          let isBooly = cut_isBoolyOp(opCode, true, ml, offset, indexR);
          if (isBooly === ML_BOOLY_NO) {
            TRACE(' - R is at least a non-booly in one op (' + ml__opName(opCode) + '), bailing');
            return;
          }
          ASSERT(isBooly === ML_BOOLY_YES, 'cannot be maybe because asked for explicit lookups');
        }
      }
    }

    TRACE(' - ok, R is booly. next confirming that R can represent any valuation of the sum args, total sum of args:', domain__debug(sum), 'R:', domain__debug(R));

    // if sum doesnt intersect with domain then there are valuations of the sum-args such that the result is not in R
    // we could theoretically fix that but it'll be too much work and little to show for. so we just bail.
    if (sum !== domain_intersection(R, sum)) {
      TRACE('  - R does not contain all possible sums so we bail');
      return false;
    }
    TRACE('  - R contains all sums so we can morph the sum to an isall');

    let args = markAndCollectArgs(ml, sumOffset, argCount);

    // so; in the remaining problem R is only used as booly. so we dont care what the actual value is of R, just
    // whether it's zero or non-zero. so it will arbitrarily be set thusly. we'll add a solveStack entry that
    // makes sure R is solved to the sum of whatever the args are solved to.
    let oR = R; // back up R because the issome may change it irrelevantly
    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - trick_sum_booly');
      // note: we need to force solve all args to make sure the sum constraint holds

      let vR = 0;
      for (let i = 0; i < argCount; ++i) {
        vR += force(args[i]);
      }
      let R = domain_intersectionValue(oR, vR);
      ASSERT(R, 'R should be able to reflect the solution');
      if (oR !== R) setDomain(indexR, R, false, true);
    });

    // the sum is a count-result-op and so is the isAll so we only need to replace the opcode
    ml_enc8(ml, sumOffset, ML_ISSOME);

    bounty_markVar(bounty, indexR);
    somethingChanged();
    return true;
  }

  function trick_issame_issame_sum(ml, sumOffset, indexR, countsR, sum, argCount) {
    // R = sum(A B), S = R ==? 1, T = R ==? 2    ->    S = A !=? B, T = all?(A B)
    // the sum is confirmed already
    // we need to confirm that this concerns 2x issame (and not 2x sum)
    // we need to confirm that each issame has R and either a literal 1 or 2 (and exactly 2 args)

    TRACE(' - trick_issame_issame_sum');
    TRACE(' - R = sum(A B), S = R ==? 1, T = R ==? 2    =>    S = A !=? B, T = all?(A B)');

    ASSERT(countsR === 3, 'should be 3 links to this sum');
    let issameOffset1 = bounty_getOffset(bounty, indexR, 0);
    let issameOffset2 = bounty_getOffset(bounty, indexR, 1);
    ASSERT(issameOffset1 === sumOffset || issameOffset2 === sumOffset || bounty_getOffset(bounty, indexR, 2) === sumOffset, 'sum should be one of the three');
    if (issameOffset1 === sumOffset) issameOffset1 = bounty_getOffset(bounty, indexR, 2);
    else if (issameOffset2 === sumOffset) issameOffset2 = bounty_getOffset(bounty, indexR, 2);

    if (ml_dec8(ml, issameOffset1) !== ML_ISSAME || ml_dec8(ml, issameOffset2) !== ML_ISSAME) {
      TRACE(' - this wasnt sum+issame+issame, bailing', ml__opName(ml_dec8(ml, issameOffset1)), ml__opName(ml_dec8(ml, issameOffset2)));
      return false;
    }

    let argCount1 = ml_dec16(ml, issameOffset1 + 1);
    let argCount2 = ml_dec16(ml, issameOffset2 + 1);

    if (argCount1 !== 2 || argCount2 !== 2) {
      TRACE(' - at least one of the issame ops does not have 2 args, bailing');
      return false;
    }

    // R = sum(A B)      R = sum(A B)
    // S = K ==? L       S = R ==? X
    // T = M ==? N       T = R ==? Y
    //    X==1&Y==2 | X==2&Y==1

    let indexA = readIndex(ml, sumOffset + OFFSET_C_A);
    let indexB = readIndex(ml, sumOffset + OFFSET_C_B);

    let A = getDomain(indexA, true);
    let B = getDomain(indexB, true);
    TRACE(' - A:', domain__debug(A), ', B:', domain__debug(B));
    if (!domain_isBool(A) || !domain_isBool(B)) {
      TRACE(' - A or B wasnt bool, bailing');
      return false;
    }

    let indexK = readIndex(ml, issameOffset1 + OFFSET_C_A);
    let indexL = readIndex(ml, issameOffset1 + OFFSET_C_B);
    let indexS = readIndex(ml, issameOffset1 + OFFSET_C_R);
    let indexM = readIndex(ml, issameOffset2 + OFFSET_C_A);
    let indexN = readIndex(ml, issameOffset2 + OFFSET_C_B);
    let indexT = readIndex(ml, issameOffset2 + OFFSET_C_R);

    ASSERT(indexK === indexR || indexL === indexR, 'R should be arg to this issame');
    let indexX = indexK;
    if (indexX === indexR) indexX = indexL;

    ASSERT(indexM === indexR || indexN === indexR, 'R should be arg to this issame');
    let indexY = indexM;
    if (indexY === indexR) indexY = indexN;

    let X = getDomain(indexX, true);
    let vX = domain_getValue(X);
    let Y = getDomain(indexY, true);
    let vY = domain_getValue(Y);

    TRACE(' - (X)  S=K==?L :', `${indexS}=${indexK}==?${indexL}`, domain__debug(getDomain(indexS, true)), '=', domain__debug(getDomain(indexK, true)), '==?', domain__debug(getDomain(indexL, true)));
    TRACE(' - (Y)  T=M==?N :', `${indexT}=${indexM}==?${indexN}`, domain__debug(getDomain(indexT, true)), '=', domain__debug(getDomain(indexM, true)), '==?', domain__debug(getDomain(indexN, true)));
    TRACE(' - X=', indexX, '=', domain__debug(X), ', Y=', indexY, '=', domain__debug(Y));

    if ((vX !== 1 && vX !== 2) || (vY !== 1 && vY !== 2) || vX === vY) {
      TRACE(' - issame pattern doesnt match, bailing');
      return false;
    }

    TRACE_MORPH('R = sum(A B), S = R ==? 1, T = R ==? 2', 'S = A !=? B, T = all?(A B)');
    TRACE(' - pattern should match now so we can start the morph. one issame becomes A!=?B, the sum becomes all?(A B), the other issame is eliminated, sum solve stack entry added for R');
    ASSERT((vX === 1 && vY === 2) || (vX === 2 && vY === 1), 'we just checked this!');

    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - trick_issame_issame_sum');
      TRACE(' - ensure the sum result and args are all solved');

      let R = getDomain(indexR);

      // A and B were confirmed to be bools
      // R is confirmed to be [0 2] (still)
      ASSERT(R === domain_createRange(0, 2));

      // force and sum the values of A and B and set R to that
      let sum = force(indexA) + force(indexB);
      let nR = domain_intersectionValue(R, sum);
      if (R !== nR) setDomain(indexR, nR);

      ASSERT(getDomain(indexA));
      ASSERT(getDomain(indexB));
      ASSERT(getDomain(indexR));
      ASSERT(domain_isSolved(getDomain(indexA)));
      ASSERT(domain_isSolved(getDomain(indexB)));
      ASSERT(domain_isSolved(getDomain(indexR)));
      ASSERT(domain_getValue(getDomain(indexR)) === domain_getValue(getDomain(indexA)) + domain_getValue(getDomain(indexB)));
    });

    // T = all?(A B)
    ml_enc8(ml, sumOffset, ML_ISALL);
    ASSERT(argCount === 2, 'change the offset below if this changes');
    ml_enc16(ml, sumOffset + OFFSET_C_C, vX === 2 ? indexS : indexT);

    // S = A !=? B
    ASSERT(ml_dec16(ml, issameOffset1 + 1) === 2, 'arg count for issame must be 2');
    ml_enc8(ml, issameOffset1, ML_ISDIFF);
    ml_enc16(ml, issameOffset1 + OFFSET_C_A, indexA);
    ml_enc16(ml, issameOffset1 + OFFSET_C_B, indexB);
    ml_enc16(ml, issameOffset1 + OFFSET_C_R, vX === 1 ? indexS : indexT);

    // drop the other issame
    ASSERT(ml_dec16(ml, issameOffset2 + 1) === 2, 'arg count for issame must be 2');
    ml_eliminate(ml, issameOffset2, SIZEOF_CR_2);

    bounty_markVar(bounty, indexA);
    bounty_markVar(bounty, indexB);
    bounty_markVar(bounty, indexR);
    bounty_markVar(bounty, indexS);
    bounty_markVar(bounty, indexX);
    bounty_markVar(bounty, indexT);
    bounty_markVar(bounty, indexY);
    somethingChanged();

    return true;
  }

  // ##############

  function cut_isBoolyOp(opCode, checkMaybes, ml, offset, index) {
    TRACE(' - cut_isBoolyOp, op=', ml__opName(opCode), ', thorough check?', checkMaybes);
    switch (opCode) {
      case ML_LT:
      case ML_LTE:
      case ML_MINUS:
      case ML_DIV:
      case ML_SUM:
      case ML_PRODUCT:
      case ML_DIFF:
      case ML_SAME:
        return ML_BOOLY_NO;

      case ML_XOR:
      case ML_XNOR:
      case ML_IMP:
      case ML_NIMP:
      case ML_ALL:
      case ML_NALL:
      case ML_SOME:
      case ML_NONE:
        return ML_BOOLY_YES;

      case ML_NOLEAF:
        return ML_BOOLY_YES;
      case ML_NOBOOL:
        return ML_BOOLY_NO;

      case ML_ISDIFF:
      case ML_ISSAME:
        // if the var occurs as any of the args, it is not a booly (regardless)
        if (!checkMaybes) return ML_BOOLY_MAYBE;
        TRACE('   - thorough check for', ml__opName(opCode), 'on index=', index);
        let argCount = ml_dec16(ml, offset + 1);
        for (let i = 0; i < argCount; ++i) {
          if (readIndex(ml, offset + SIZEOF_C + i * 2) === index) return ML_BOOLY_NO;
        }
        ASSERT(readIndex(ml, offset + SIZEOF_C + argCount * 2) === index, 'if none of the args is index then R must be index');
        return ML_BOOLY_YES;

      case ML_ISLT:
      case ML_ISLTE:
        // for these ops the result var is fixed in third position
        if (!checkMaybes) return ML_BOOLY_MAYBE;
        TRACE('   - thorough check for', ml__opName(opCode), 'on index=', index);
        if (readIndex(ml, offset + 1) === index || readIndex(ml, offset + 3) === index) return ML_BOOLY_NO;
        ASSERT(readIndex(ml, offset + 5) === index, 'if neither arg then index must be result');
        return ML_BOOLY_YES;

      case ML_ISALL:
      case ML_ISNALL:
      case ML_ISSOME:
      case ML_ISNONE:
        return ML_BOOLY_YES;

      case ML_START:
      case ML_JMP:
      case ML_JMP32:
      case ML_NOOP:
      case ML_NOOP2:
      case ML_NOOP3:
      case ML_NOOP4:
      case ML_STOP:
        return THROW('should not be used for these ops');

      default:
        TRACE('(ml_isBooly) unknown op: ' + opCode);
        THROW('(ml_isBooly) unknown op: ' + opCode);
    }
  }

  function removeOneConstantFromArgs(constantValue, constantArgIndex, argCount, sumOffset) {
    TRACE(' - removeOneConstantFromArgs; only if there is at most one constant at all; const value:', constantValue, ', arg pos:', constantArgIndex, ', args:', argCount, ', op offset:', sumOffset);
    ASSERT(constantArgIndex < argCount, 'arg pos should be valid');
    if (constantArgIndex >= 0) {
      // we want to eliminate the constant arg
      // it may not be in last position (it ought to be but *shrug*), if so simply overwrite it by the last element
      if (constantArgIndex !== argCount - 1) {
        TRACE(' - constant wasnt at end, moving it there now, index=', constantArgIndex, ', argCount=', argCount);
        let lastIndex = readIndex(ml, sumOffset + SIZEOF_C + (argCount - 1) * 2);
        ml_enc16(ml, sumOffset + SIZEOF_C + constantArgIndex * 2, lastIndex);
        // we want to drop the constant so we dont need to copy that back
      }
      TRACE(' - constant is (now) at the end, reducing arg count to drop it from', argCount, 'to', argCount - 1);
      TRACE(' - op before:', ml__debug(ml, sumOffset, 1, problem));
      ASSERT(domain_getValue(getDomain(readIndex(ml, sumOffset + SIZEOF_C + (argCount - 1) * 2), true)) === constantValue, 'the constant should now be in last position of the sum');
      // reduce sum arg count
      --argCount;
      ml_enc16(ml, sumOffset + 1, argCount);
      // note: no need to copy R one position back because we will explicitly write an S there anyways
      // write a jump in the new open space
      ml_enc8(ml, sumOffset + SIZEOF_C + (argCount + 1) * 2, ML_NOOP2);

      TRACE(' - op after:', ml__debug(ml, sumOffset, 1, problem));
      ASSERT(ml_validateSkeleton(ml, 'removeOneConstantFromArgs; after constant elimination'));
    }
    return argCount;
  }
  function addSumToSolveStack(indexR, args, constantValue) {
    TRACE(' - adding solvestack entry for isnone/isall/issome/isnall');
    TRACE(' - args sum to', domain__debug(args.map(getDomain).reduce((a, b) => domain_plus(a, b))), ', constant:', constantValue, ', total:', domain__debug(domain_plus(domain_createValue(constantValue), args.map(getDomain).reduce((a, b) => domain_plus(a, b)))), ', R=', domain__debug(getDomain(indexR)), ', all args:', args.map(getDomain).map(domain__debug).join(' '));
    ASSERT(domain_intersection(getDomain(indexR), domain_plus(domain_createValue(constantValue), args.map(getDomain).reduce((a, b) => domain_plus(a, b)))) === getDomain(indexR), 'R should be able to reflect the outcome of summing any of its args');

    // note: either way, R must reflect the sum of its args. so its the same solve
    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - addSumToSolveStack; cut sum+reifier -> isnone/issome/isall/isnall');
      let oR = getDomain(indexR);
      let vR = 0;
      for (let i = 0, n = args.length; i < n; ++i) {
        let vN = force(args[i]);
        ASSERT((vN & 1) >= 0, 'should be bool');
        if (vN) ++vR;
      }
      let R = domain_intersectionValue(oR, vR + constantValue);
      ASSERT(R, 'R should be able to reflect the solution');
      if (oR !== R) setDomain(indexR, R);
    });
  }

  function cutAddPseudoBoolyAlias(indexKeep, indexEliminate) {
    let oE = getDomain(indexEliminate, true); // remember what E was because it will be replaced by false to mark it an alias
    TRACE(' - pseudo-alias for booly xnor arg;', indexKeep, '@', indexEliminate, '  ->  ', domain__debug(getDomain(indexKeep)), '@', domain__debug(getDomain(indexEliminate)), 'replacing', indexEliminate, 'with', indexKeep);

    let XNOR_EXCEPTION = true;
    solveStack.push((_, force, getDomain, setDomain) => {
      TRACE(' - cutAddPseudoBoolyAlias');
      TRACE(' -', indexKeep, '!^', indexEliminate, '  ->  ', domain__debug(getDomain(indexKeep)), '!^', domain__debug(oE));
      let vK = force(indexKeep);
      let E;
      if (vK === 0) {
        E = domain_removeGtUnsafe(oE, 0);
      } else {
        E = domain_removeValue(oE, 0);
      }
      TRACE('  -> updating', domain__debug(oE), 'to', domain__debug(E));
      ASSERT(E, 'E should be able to reflect the solution');
      // always set it even if oE==E
      setDomain(indexEliminate, E, true, XNOR_EXCEPTION);
    });

    // note: addAlias will push a defer as well. since the defers are resolved in reverse order,
    // we must call addAlias after adding our own defer, otherwise our change will be lost.
    addAlias(indexEliminate, indexKeep, 'cutAddPseudoBoolyAlias');
  }

  function markAndCollectArgs(ml, opOffset, argCount, except = -1) {
    TRACE(' - markAndCollectArgs, from offset', opOffset, 'for', argCount, 'vars');
    let args = [];
    for (let i = 0; i < argCount; ++i) {
      let index = readIndex(ml, opOffset + SIZEOF_C + i * 2);
      if (index !== except) args.push(index);
      bounty_markVar(bounty, index);
    }
    return args;
  }
  function markAllArgs(ml, opOffset, argCount) {
    for (let i = 0; i < argCount; ++i) {
      let index = readIndex(ml, opOffset + SIZEOF_C + i * 2);
      bounty_markVar(bounty, index);
    }
  }

  function cut_moveTo(ml, offset, len) {
    TRACE(' - trying to move from', offset, 'to', offset + len, 'delta = ', len);
    switch (ml_dec8(ml, offset + len)) {
      case ML_NOOP:
      case ML_NOOP2:
      case ML_NOOP3:
      case ML_NOOP4:
      case ML_JMP:
      case ML_JMP32:
        TRACE('  - moving to another jump so merging them now');
        ml_compileJumpAndConsolidate(ml, offset, len);
        pc = offset; // restart, make sure the merge worked
        break;
      default:
        pc = offset + len;
        break;
    }
  }
}

// BODY_STOP

export {
  cutter,
};
