// problem optimizer
// take an input problem and determine whether constraints can be pruned
// or domains cut before actually generating their propagators

import {
  $CHANGED,
  $REJECTED,
  $SOLVED,
  $STABLE,

  ASSERT,
  ASSERT_NORDOM,
  getTerm,
  TRACE,
  TRACE_MORPH,
  THROW,
} from '../../fdlib/src/helpers';
import {
  domain__debug,
  domain_createEmpty,
  domain_createBoolyPair,
  domain_createValue,
  domain_divby,
  domain_getValue,
  domain_hasNoZero,
  domain_hasZero,
  domain_intersection,
  domain_intersectionValue,
  domain_invMul,
  domain_isBool,
  domain_isBooly,
  domain_isBoolyPair,
  domain_isSolved,
  domain_isZero,
  domain_max,
  domain_min,
  domain_minus,
  domain_mul,
  domain_plus,
  domain_removeGte,
  domain_removeGtUnsafe,
  domain_removeLte,
  domain_removeLtUnsafe,
  domain_removeValue,
  domain_sharesNoElements,
  domain_size,
} from '../../fdlib/src/domain';

import {
  ML_ALL,
  ML_NOLEAF,
  ML_NOBOOL,
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

  OFFSET_C_A,
  OFFSET_C_B,
  //OFFSET_C_C,
  OFFSET_C_R,

  SIZEOF_V,
  SIZEOF_W,
  SIZEOF_VVV,
  SIZEOF_C,
  SIZEOF_C_2,
  SIZEOF_CR_2,

  ml__debug,
  ml__opName,
  ml_c2c2,
  ml_cr2c2,
  ml_cr2cr2,
  ml_dec8,
  ml_dec16,
  ml_dec32,
  ml_enc8,
  ml_enc16,
  ml_eliminate,
  ml_compileJumpAndConsolidate,
  ml_compileJumpSafe,
  ml_heapSort16bitInline,
  ml_validateSkeleton,
  ml_vvv2c2,
} from './ml';
import {
  m2d__debug,
} from './ml2dsl';

// BODY_START

function min_run(ml, problem, domains, names, firstRun, once) {
  TRACE('min_run, loop:', firstRun, ', byte code:', ml.length < 50 ? ml.join(' ') : '<big>');
  TRACE(ml__debug(ml, 0, 20, problem));

  // now we can access the ml in terms of bytes, jeuj
  let state = min_optimizeConstraints(ml, problem, domains, names, firstRun, once);
  if (state === $SOLVED) {
    TRACE('minimizing solved it!', state); // all constraints have been eliminated
  } else if (state === $REJECTED) {
    TRACE('minimizing rejected it!', state); // an empty domain was found or a literal failed a test
  } else {
    TRACE('pre-optimization finished, not yet solved');
  }

  return state;
}

function min_optimizeConstraints(ml, problem, domains, names, firstRun, once) {
  TRACE('min_optimizeConstraints', ml.length < 50 ? ml.join(' ') : '');
  TRACE(problem.domains.length > 100 ? '' : '  <' + problem.domains.map((d, i) => i + ' : ' + problem.varNames[i] + ' : ' + domain__debug(problem.getDomain(i))).join('>, <') + '>');
  TRACE('minimize sweep, ml len=', ml.length, ', firstRun=', firstRun, 'once=', once);
  let varChanged = true;
  let onlyJumps = false;
  let emptyDomain = false;
  let lastPcOffset = 0;
  let lastOp = 0;
  let pc = 0;
  let loops = 0;
  let constraints = 0; // count a constraint going forward, ignore jumps, reduce when restarting from same pc
  let restartedRelevantOp = false; // annoying, but restartedRelevantOp could mean more scrubbing is required. but it may not...

  let term = getTerm();

  let {
    addVar,
    addAlias,
    getAlias,
    getDomain,
    setDomain,
    solveStack,
  } = problem;

  //function addPseudoAlias(indexA, indexB, A, B) {
  //  ASSERT(domain_isBoolyPair(A) && domain_isBoolyPair(B), 'assuming A and B are booly pairs');
  //  ASSERT(A !== B, 'booly pairs that are equal are regular aliases so dont call this function on them');
  //
  //  addAlias(indexA, indexB); // A is replaced by B
  //
  //  // consider them aliases but add a special solve stack
  //  // entry to restore the max to A if B turns out nonzero
  //  solveStack.push((_, force, getDomain, setDomain) => {
  //    TRACE(' - deduper psuedo alias; was:', domain__debug(A), '!^', domain__debug(B), ', now:', domain__debug(getDomain(indexA)), '!^', domain__debug(getDomain(indexB)));
  //    let vB = force(indexB);
  //    TRACE(' - B forced to', vB);
  //    if (vB > 0) {
  //      setDomain(indexA, domain_removeValue(A, 0), true, true);
  //    }
  //
  //    ASSERT(getDomain(indexA));
  //    ASSERT(getDomain(indexB));
  //    ASSERT(domain_isSolved(getDomain(indexA)));
  //    ASSERT(domain_isSolved(getDomain(indexB)));
  //    ASSERT((domain_getValue(getDomain(indexA)) === 0) === (domain_getValue(getDomain(indexB)) === 0));
  //  });
  //}

  while (!onlyJumps && (varChanged || restartedRelevantOp)) {
    ++loops;
    //term.log('- looping', loops);
    term.time('-> min_loop ' + loops);
    TRACE('min outer loop');
    varChanged = false;
    onlyJumps = true; // until proven otherwise
    restartedRelevantOp = false;
    pc = 0;
    constraints = 0;
    let ops = min_innerLoop();
    TRACE('changed?', varChanged, 'only jumps?', onlyJumps, 'empty domain?', emptyDomain, 'restartedRelevantOp?', restartedRelevantOp);
    if (emptyDomain) {
      term.log('Empty domain at', lastPcOffset, 'for opcode', lastOp, [ml__debug(ml, lastPcOffset, 1, problem)], ml.slice(lastPcOffset, lastPcOffset + 10));
      term.error('Empty domain, problem rejected');
    }
    term.timeEnd('-> min_loop ' + loops);
    term.log('   - ops this loop:', ops, 'constraints:', constraints);
    if (emptyDomain) return $REJECTED;
    if (onlyJumps) return $SOLVED;

    TRACE('\n## Intermediate state: ##');
    TRACE(ml__debug(ml, 0, 20, problem));
    TRACE(m2d__debug(problem));

    if (once) break;
    firstRun = false;
  }
  if (loops === 1) return $STABLE;
  return $CHANGED;

  // ####################################################################################

  function readIndex(ml, offset) {
    // get an index from ml. check for alias, and if so, immediately compile back the alias to improve future fetches.
    let index = ml_dec16(ml, offset);
    let alias = getAlias(index);
    if (alias !== index) ml_enc16(ml, offset, alias);
    return alias;
  }

  function getDomainFast(index) {
    ASSERT(index >= 0 && index <= 0xffff, 'expecting valid index', index);
    ASSERT(getAlias(index) === index, 'index should be unaliased', index, getAlias(index));

    let domain = getDomain(index, true);
    ASSERT(domain, 'domain cant be falsy', domain);
    ASSERT_NORDOM(domain);

    if (!domain) setEmpty(index, 'bad state (empty domain should have been detected sooner)');
    return domain;
  }

  function updateDomain(index, domain, desc) {
    TRACE(' - updateDomain; {', index, '} updated from', domain__debug(getDomain(index)), 'to', domain__debug(domain));
    ASSERT(!domain || domain_intersection(getDomain(index), domain), 'should never add new values to a domain, only remove them', 'index=', index, 'old=', domain__debug(getDomain(index)), 'new=', domain__debug(domain), 'desc=', desc);


    setDomain(index, domain, false, true);

    if (domain) {
      varChanged = true;
    } else {
      TRACE(' - (updateDomain: EMPTY DOMAIN)');
      emptyDomain = true;
    }

    return emptyDomain;
  }

  function setEmpty(index, desc) {
    TRACE(' - :\'( setEmpty({', index, '})', desc);
    emptyDomain = true;
    if (index >= 0) updateDomain(index, domain_createEmpty(), 'explicitly empty' + (desc ? '; ' + desc : ''));
  }

  function min_innerLoop() {
    let ops = 0;
    onlyJumps = true;
    let wasMetaOp = false; // jumps, start, stop, etc. not important if they "change"
    while (pc < ml.length && !emptyDomain) {
      ++ops;
      ++constraints;
      wasMetaOp = false;
      let pcStart = pc;
      lastPcOffset = pc;
      let op = ml[pc];
      lastOp = op;

      //ASSERT(ml_validateSkeleton(ml, 'min_innerLoop'));

      TRACE(' # CU pc=' + pcStart, ', op=', op, ml__opName(op));
      TRACE(' -> op: ' + ml__debug(ml, pc, 1, problem, true));

      switch (op) {
        case ML_START:
          if (pc !== 0) {
            TRACE('reading a op=zero at position ' + pc + ' which should not happen', ml.slice(Math.max(pc - 100, 0), pc), '<here>', ml.slice(pc, pc + 100));
            return THROW(' ! optimizer problem @', pc);
          }
          wasMetaOp = true;
          ++pc;
          --constraints; // not a constraint
          break;

        case ML_STOP:
          TRACE(' ! good end @', pcStart);
          wasMetaOp = true;
          --constraints; // not a constraint
          return ops;

        case ML_LT:
          TRACE('- lt vv @', pcStart);
          min_lt(ml, pc);
          break;

        case ML_LTE:
          TRACE('- lte vv @', pcStart);
          min_lte(ml, pc);
          break;

        case ML_NONE:
          TRACE('- none @', pcStart);
          min_none(ml, pc);
          break;

        case ML_XOR:
          TRACE('- xor @', pcStart);
          min_xor(ml, pc);
          break;

        case ML_XNOR:
          TRACE('- xnor @', pcStart);
          min_xnor(ml, pc);
          break;

        case ML_IMP:
          TRACE('- imp @', pcStart);
          min_imp(ml, pc);
          break;

        case ML_NIMP:
          TRACE('- nimp @', pcStart);
          min_nimp(ml, pc);
          break;

        case ML_DIFF:
          TRACE('- diff @', pcStart);
          min_diff(ml, pc);
          break;

        case ML_ALL:
          TRACE('- all() @', pcStart);
          min_all(ml, pc);
          break;

        case ML_ISDIFF:
          TRACE('- isdiff @', pcStart);
          min_isDiff(ml, pc);
          break;

        case ML_NALL:
          TRACE('- nall @', pcStart);
          min_nall(ml, pc);
          break;

        case ML_SAME:
          TRACE('- same @', pcStart);
          min_same(ml, pc);
          break;

        case ML_SOME:
          TRACE('- some @', pcStart);
          min_some(ml, pc);
          break;

        case ML_ISLT:
          TRACE('- islt vvv @', pcStart);
          min_isLt(ml, pc);
          break;

        case ML_ISLTE:
          TRACE('- islte vvv @', pcStart);
          min_isLte(ml, pc);
          break;

        case ML_ISALL:
          TRACE('- isall @', pcStart);
          min_isAll(ml, pc);
          break;

        case ML_ISNALL:
          TRACE('- isnall @', pcStart);
          min_isNall(ml, pc);
          break;

        case ML_ISSAME:
          TRACE('- issame @', pcStart);
          min_isSame(ml, pc);
          break;

        case ML_ISSOME:
          TRACE('- issome @', pcStart);
          min_isSome(ml, pc);
          break;

        case ML_ISNONE:
          TRACE('- isnone @', pcStart);
          min_isNone(ml, pc);
          break;

        case ML_MINUS:
          TRACE('- minus @', pcStart);
          min_minus(ml, pc);
          break;

        case ML_DIV:
          TRACE('- div @', pcStart);
          min_div(ml, pc);
          break;

        case ML_SUM:
          TRACE('- sum @', pcStart);
          min_sum(ml, pc);
          break;

        case ML_PRODUCT:
          TRACE('- product @', pcStart);
          min_product(ml, pc);
          break;

        case ML_NOBOOL:
          TRACE('- nobool @', pc);
          pc += SIZEOF_V;
          wasMetaOp = true;
          break;
        case ML_NOLEAF:
          TRACE('- noleaf @', pc);
          pc += SIZEOF_V;
          wasMetaOp = true;
          break;

        case ML_NOOP:
          TRACE('- noop @', pc);
          min_moveTo(ml, pc, 1);
          --constraints; // not a constraint
          wasMetaOp = true;
          break;
        case ML_NOOP2:
          TRACE('- noop2 @', pc);
          min_moveTo(ml, pc, 2);
          --constraints; // not a constraint
          wasMetaOp = true;
          break;
        case ML_NOOP3:
          TRACE('- noop3 @', pc);
          min_moveTo(ml, pc, 3);
          --constraints; // not a constraint
          wasMetaOp = true;
          break;
        case ML_NOOP4:
          TRACE('- noop4 @', pc);
          min_moveTo(ml, pc, 4);
          --constraints; // not a constraint
          wasMetaOp = true;
          break;
        case ML_JMP:
          TRACE('- jmp @', pc);
          min_moveTo(ml, pc, SIZEOF_V + ml_dec16(ml, pc + 1));
          --constraints; // not a constraint
          wasMetaOp = true;
          break;
        case ML_JMP32:
          TRACE('- jmp32 @', pc);
          min_moveTo(ml, pc, SIZEOF_W + ml_dec32(ml, pc + 1));
          --constraints; // not a constraint
          wasMetaOp = true;
          break;

        default:
          THROW('(mn) unknown op: 0x' + op.toString(16), ' at', pc);
      }

      if (pc === pcStart && !emptyDomain) {
        TRACE(' - restarting op from same pc...');
        if (!wasMetaOp) restartedRelevantOp = true; // TODO: undo this particular step if the restart results in the offset becoming a jmp?
        --constraints; // constraint may have been eliminated
      }
    }
    if (emptyDomain) {
      return ops;
    }
    return THROW('Derailed; expected to find STOP before EOF');
  }

  function min_moveTo(ml, offset, len) {
    TRACE(' - trying to move from', offset, 'to', offset + len, 'delta = ', len);
    switch (ml_dec8(ml, offset + len)) {
      case ML_NOOP:
      case ML_NOOP2:
      case ML_NOOP3:
      case ML_NOOP4:
      case ML_JMP:
      case ML_JMP32:
        TRACE('- moving to another jump so merging them now');
        ml_compileJumpAndConsolidate(ml, offset, len);
        pc = offset; // restart, make sure the merge worked
        break;
      default:
        pc = offset + len;
        break;
    }
  }

  function min_same(ml, offset) {
    // loop through the args and alias each one to the previous. then eliminate the constraint. it is an artifact.
    let argCount = ml_dec16(ml, offset + 1);

    TRACE(' = min_same', argCount, 'x');

    if (argCount === 2) {
      if (readIndex(ml, offset + OFFSET_C_A) === readIndex(ml, offset + OFFSET_C_B)) {
        TRACE(' - argcount=2 and A==B so eliminating constraint');
        ml_eliminate(ml, offset, SIZEOF_C_2);
        return;
      }
    }

    if (argCount > 1) {
      TRACE(' - aliasing all args to the first arg, intersecting all domains, and eliminating constraint');
      let firstIndex = readIndex(ml, offset + SIZEOF_C);
      let F = getDomain(firstIndex, true);

      TRACE(' - indexF=', firstIndex, ', F=', domain__debug(F));

      for (let i = 1; i < argCount; ++i) {
        let indexD = readIndex(ml, offset + SIZEOF_C + i * 2);
        if (indexD !== firstIndex) {
          let D = getDomain(indexD, true);
          TRACE('   - pos:', i, ', aliasing index', indexD, 'to F, intersecting', domain__debug(D), 'with', domain__debug(F), 'to', domain__debug(domain_intersection(F, D)));
          F = intersectAndAlias(indexD, firstIndex, D, F);
          if (!F) {
            TRACE('   !! Caused an empty domain. Failing.');
            break;
          }
        }
      }
    }

    TRACE(' - eliminating same() constraint');
    ml_eliminate(ml, offset, SIZEOF_C + argCount * 2);
  }

  function min_diff_2(ml, offset) {
    TRACE(' - min_diff_2');
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'should be arg count = 2');

    let offsetA = offset + OFFSET_C_A;
    let offsetB = offset + OFFSET_C_B;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);

    TRACE(' -', indexA, '!=', indexB, '   ->   ', domain__debug(A), '!=', domain__debug(B));
    if (!A || !B) return true;
    if (indexA === indexB) {
      TRACE(' - A != A, falsum, artifact case');
      setEmpty(indexA, 'X!=X falsum');
      return true;
    }

    let solved = false;

    // if either is solved then the other domain should
    // become the result of unsolved_set "minus" solved_set
    let vA = domain_getValue(A);
    if (vA >= 0) {
      let oB = B;
      B = domain_removeValue(B, vA);
      if (oB !== B && updateDomain(indexB, B, 'A != B with A solved')) return true;
      solved = true;
    } else {
      let vB = domain_getValue(B);
      if (domain_getValue(B) >= 0) {
        let oA = A;
        A = domain_removeValue(A, vB);
        if (A !== oA && updateDomain(indexA, A, 'A != B with B solved')) return true;
        solved = true;
      }
    }

    // if the two domains share no elements the constraint is already satisfied
    if (!solved && !domain_intersection(A, B)) solved = true;

    TRACE(' ->', domain__debug(A), '!=', domain__debug(B), ', solved?', solved);

    // solved if the two domains (now) intersect to an empty domain
    if (solved) {
      TRACE(' - No element overlapping between', indexA, 'and', indexB, 'left so we can eliminate this diff');
      ASSERT(domain_sharesNoElements(A, B), 'if A or B solves, the code should have solved the diff');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    TRACE(' - min_diff_2 changed nothing');
    return false;
  }

  function min_lt(ml, offset) {
    let offsetA = offset + OFFSET_C_A;
    let offsetB = offset + OFFSET_C_B;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);

    TRACE(' = min_lt', indexA, '<', indexB, '   ->   ', domain__debug(A), '<', domain__debug(B));
    if (indexA === indexB) return setEmpty(indexA, 'X<X falsum'); // (relevant) artifact case
    if (!A || !B) return;

    // relative comparison is easy; cut away any non-intersecting
    // values that violate the desired outcome. only when a A and
    // B have multiple intersecting values we have to keep this
    // constraint
    let oA = A;
    A = domain_removeGte(A, domain_max(B));
    if (A !== oA) {
      TRACE(' - updating A to', domain__debug(A));
      if (updateDomain(indexA, A, 'A lt B')) return;
    }

    let oB = B;
    B = domain_removeLte(B, domain_min(A));
    if (B !== oB) {
      TRACE(' - updating B to', domain__debug(B));
      if (updateDomain(indexB, B, 'A lt B')) return;
    }

    // any value in A must be < any value in B
    if (domain_max(A) < domain_min(B)) {
      TRACE(' - Eliminating lt because max(A)<min(B)');
      ml_eliminate(ml, offset, SIZEOF_C_2);
    } else {
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + SIZEOF_C_2;
    }
  }

  function min_lte(ml, offset) {
    let offsetA = offset + OFFSET_C_A;
    let offsetB = offset + OFFSET_C_B;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);

    TRACE(' = min_lte', indexA, '<=', indexB, '   ->   ', domain__debug(A), '<=', domain__debug(B));
    if (!A || !B) return;

    if (indexA === indexB) {
      TRACE(' - Eliminating lte because max(A)<=min(A) is a tautology (once solved)');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    // relative comparison is easy; cut away any non-intersecting
    // values that violate the desired outcome. only when a A and
    // B have multiple intersecting values we have to keep this
    // constraint

    TRACE(' - index A!=B so remove all >max(B) from A', domain__debug(A), domain_max(B), '->', domain__debug(domain_removeGtUnsafe(A, domain_max(B))));

    let oA = A;
    A = domain_removeGtUnsafe(A, domain_max(B));
    if (A !== oA) {
      TRACE(' - Updating A to', domain__debug(A));
      if (updateDomain(indexA, A, 'A lte B')) return;
    }

    // A is (now) empty so just remove it
    let oB = B;
    B = domain_removeLtUnsafe(B, domain_min(A));
    if (B !== oB) {
      TRACE(' - Updating B to', domain__debug(B));
      if (updateDomain(indexB, B, 'A lte B')) return;
    }

    TRACE(' ->', domain__debug(A), '<=', domain__debug(B), ', bp?', domain_isBoolyPair(A), '<=', domain_isBoolyPair(B), ', max:', domain_max(A), '<=', domain_max(B));

    // any value in A must be < any value in B
    if (domain_max(A) <= domain_min(B)) {
      TRACE(' - Eliminating lte because max(A)<=min(B)');
      ml_eliminate(ml, offset, SIZEOF_C_2);
    } else if (domain_isBoolyPair(A) && domain_isBoolyPair(B) && domain_max(A) <= domain_max(B)) {
      TRACE(' - A and B boolypair with max(A)<=max(B) so this is implication');
      TRACE_MORPH('A <= B', 'B -> A');
      ml_c2c2(ml, offset, 2, ML_IMP, indexA, indexB);
      // have to add a solvestack entry to prevent a solution [01]->1 which would satisfy IMP but not LTE
      solveStack.push((_, force, getDomain, setDomain) => {
        TRACE(' - min_lte; enforcing LTE', indexA, '<=', indexB, ' => ', domain__debug(getDomain(indexA)), '<=', domain__debug(getDomain(indexB)));
        let A = getDomain(indexA);
        let B = getDomain(indexB);

        if (domain_hasNoZero(A)) {
          B = domain_removeValue(B, 0);
          setDomain(indexB, B);
        } else if (domain_isZero(B) || domain_isBooly(A)) {
          A = domain_removeGtUnsafe(A, 0);
          setDomain(indexA, A);
        }
        ASSERT(getDomain(indexA));
        ASSERT(getDomain(indexB));
        ASSERT(domain_max(getDomain(indexA)) <= domain_min(getDomain(indexB)), 'must hold lte', domain__debug(A), '<=', domain__debug(B));
      });
    } else {
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + SIZEOF_C_2;
    }
  }

  function min_nall(ml, offset) {
    let offsetCount = offset + 1;
    let argCount = ml_dec16(ml, offsetCount);
    let offsetArgs = offset + SIZEOF_C;
    let opSize = SIZEOF_C + argCount * 2;

    TRACE(' = min_nall', argCount, 'x');
    TRACE('  - ml for this nall:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  -', Array.from(Array(argCount)).map((n, i) => readIndex(ml, offsetArgs + i * 2)));
    TRACE('  -', Array.from(Array(argCount)).map((n, i) => domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)))));

    if (!argCount) return setEmpty(-1, 'nall without args is probably a bug');

    if (argCount === 2) {
      if (min_nall_2(ml, offset)) return;
    }

    let countStart = argCount;
    let lastIndex = -1;
    let lastDomain;

    // a nall only ensures at least one of its arg solves to zero
    for (let i = argCount - 1; i >= 0; --i) { // backwards because we're pruning dud indexes
      let index = readIndex(ml, offsetArgs + i * 2);
      let domain = getDomainFast(index);

      TRACE('  - loop i=', i, 'index=', index, 'domain=', domain__debug(domain));
      if (!domain) return;

      if (domain_min(domain) > 0 || lastIndex === index) {
        // remove var from list
        TRACE(lastIndex === index ? ' - removing redundant dupe var from nall' : ' - domain contains no zero so remove var from this constraint');

        // now
        // - move all indexes bigger than the current back one position
        // - compile the new count back in
        // - compile a NOOP in the place of the last element
        TRACE('  - moving further domains one space forward (from ', i + 1, ' / ', argCount, ')');
        min_spliceArgSlow(ml, offsetArgs, argCount, i, false);
        --argCount;
      } else if (domain_isZero(domain)) {
        // remove constraint
        TRACE(' - domain solved to zero so constraint is satisfied');
        ml_eliminate(ml, offset, SIZEOF_C + 2 * countStart);
        return;
      } else {
        // arg contains a 0 and is unsolved
        TRACE(' - domain contains zero and is not solved so leave it alone');
        lastIndex = index;
        lastDomain = domain;
      }
    }

    if (argCount === 0) {
      TRACE(' - Nall has no var left to be zero; rejecting problem');
      // this is a bad state: all vars were removed from this constraint which
      // means none of the args were zero and the constraint doesnt hold
      return setEmpty(lastIndex, 'nall; none of the args were zero');
    } else if (argCount === 1) {
      TRACE(' - Nall has one var left; forcing it to zero');
      // force set last index to zero and remove constraint. this should not
      // reject (because then the var would have been removed in loop above)
      // but do it "safe" anyways, just in case.
      let domain = domain_removeGtUnsafe(lastDomain, 0);
      if (lastDomain !== domain && updateDomain(lastIndex, domain)) return;
      ml_eliminate(ml, offset, SIZEOF_C + 2 * countStart);
    } else if (countStart !== argCount) {
      TRACE(' - recording new argcount and freeing up space');
      ml_enc16(ml, offsetCount, argCount); // write new count
      let free = (countStart - argCount) * 2;
      ml_compileJumpSafe(ml, offset + opSize - free, free);
      // note: still have to restart op because ml_jump may have clobbered the old end of the op with a new jump
    } else {
      TRACE(' - not only jumps...');

      onlyJumps = false;
      pc = offset + opSize;
    }
  }
  function min_nall_2(ml, offset) {
    let offsetA = offset + OFFSET_C_A;
    let offsetB = offset + OFFSET_C_B;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);

    TRACE(' = min_nall_2', indexA, '!&', indexB, '   ->   ', domain__debug(A), '!&', domain__debug(B));
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'nall should have 2 args');
    if (!A || !B) return true;

    if (indexA === indexB) {
      TRACE(' - indexA==indexB so A=0 and eliminate constraint');
      let oA = A;
      A = domain_removeGtUnsafe(A, 0);
      if (A !== oA) updateDomain(indexA, A, '`A !& A` means A must be zero');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    if (domain_isZero(A) || domain_isZero(B)) {
      TRACE(' - A=0 or B=0, eliminating constraint');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    if (domain_hasNoZero(A)) {
      TRACE(' - A>=1 so B must be 0');
      let oB = B;
      B = domain_removeGtUnsafe(B, 0);
      if (B !== oB) updateDomain(indexB, B, 'nall[2] B');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    if (domain_hasNoZero(B)) {
      TRACE(' - B>=1 so A must be 0');
      let oA = A;
      A = domain_removeGtUnsafe(A, 0);
      if (A !== oA) updateDomain(indexA, A, 'nall[2] A');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    TRACE(' - min_nall_2 changed nothing');
    return false;
  }

  function min_some(ml, offset) {
    let offsetCount = offset + 1;
    let argCount = ml_dec16(ml, offsetCount);
    let offsetArgs = offset + SIZEOF_C;
    let opSize = SIZEOF_C + argCount * 2;

    TRACE(' = min_some', argCount, 'x');
    TRACE('  - ml for this some:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  -', Array.from(Array(argCount)).map((n, i) => readIndex(ml, offsetArgs + i * 2)));
    TRACE('  -', Array.from(Array(argCount)).map((n, i) => domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)))));

    if (!argCount) return setEmpty(-1, 'some without args is probably a bug');

    if (argCount === 2) {
      if (min_some_2(ml, offset)) return;
    }

    let countStart = argCount;
    let lastIndex = -1;
    let lastDomain;

    // a some only ensures at least one of its arg solves to zero
    for (let i = argCount - 1; i >= 0; --i) { // backwards because we're pruning dud indexes
      let index = readIndex(ml, offsetArgs + i * 2);
      let domain = getDomainFast(index);

      TRACE('  - loop i=', i, 'index=', index, 'domain=', domain__debug(domain));
      if (!domain) return;

      if (domain_isZero(domain) || lastIndex === index) {
        // remove var from list
        TRACE(lastIndex === index ? ' - removing redundant dupe var from some' : ' - domain contains no zero so remove var from this constraint');

        // now
        // - move all indexes bigger than the current back one position
        // - compile the new count back in
        // - compile a NOOP in the place of the last element
        TRACE('  - moving further domains one space forward (from ', i + 1, ' / ', argCount, ')');
        min_spliceArgSlow(ml, offsetArgs, argCount, i, false);
        --argCount;
      } else if (domain_hasNoZero(domain)) {
        // remove constraint
        TRACE(' - domain solved to nonzero so constraint is satisfied');
        ml_eliminate(ml, offset, SIZEOF_C + 2 * countStart);
        return;
      } else {
        // arg contains a 0 and is unsolved
        TRACE(' - domain contains zero and is not solved so leave it alone');
        lastIndex = index;
        lastDomain = domain;
      }
    }

    if (argCount === 0) {
      TRACE(' - Some has no var left to be zero; rejecting problem');
      // this is a bad state: all vars were removed from this constraint which
      // means all of the args were zero and the constraint doesnt hold
      return setEmpty(lastIndex, 'some; all of the args were zero');
    } else if (argCount === 1) {
      TRACE(' - Some has one var left; forcing it to nonzero');
      // force set last index to nonzero and remove constraint. this should not
      // reject (because then the var would have been removed in loop above)
      // but do it "safe" anyways, just in case.
      let domain = domain_removeValue(lastDomain, 0);
      if (lastDomain !== domain && updateDomain(lastIndex, domain)) return;
      ml_eliminate(ml, offset, SIZEOF_C + 2 * countStart);
    } else if (countStart !== argCount) {
      TRACE(' - recording new argcount and freeing up space');
      ml_enc16(ml, offsetCount, argCount); // write new count
      let free = (countStart - argCount) * 2;
      ml_compileJumpSafe(ml, offset + opSize - free, free);
      // note: still have to restart op because ml_jump may have clobbered the old end of the op with a new jump
    } else {
      TRACE(' - not only jumps...');

      onlyJumps = false;
      pc = offset + opSize;
    }
  }

  function min_isAll(ml, offset) {
    let offsetCount = offset + 1;
    let argCount = ml_dec16(ml, offsetCount);
    let opSize = SIZEOF_C + 2 + argCount * 2;
    let offsetArgs = offset + SIZEOF_C;
    let offsetR = offset + opSize - 2;

    let indexR = readIndex(ml, offsetR);
    let R = getDomainFast(indexR);

    TRACE(' = min_isAll', argCount, 'x');
    TRACE('  - ml for this isAll (' + opSize + 'b):', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  -', indexR, '= all?(', Array.from(Array(argCount)).map((n, i) => readIndex(ml, offsetArgs + i * 2)), ')');
    TRACE('  -', domain__debug(R), '= all?(', Array.from(Array(argCount)).map((n, i) => domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)))), ')');

    if (!R) return;

    if (domain_isZero(R)) {
      TRACE(' - R is 0 so morph to nall and revisit');
      // compile to nall and revisit
      ml_enc8(ml, offset, ML_NALL);
      ml_compileJumpSafe(ml, offset + opSize - 2, 2); // difference between nall with R=0 and an isAll is the result var (16bit)
      return;
    }

    if (domain_hasNoZero(R)) {
      TRACE(' - R is non-zero so remove zero from all args and eliminate constraint');
      for (let i = 0; i < argCount; ++i) {
        let index = readIndex(ml, offsetArgs + i * 2);
        let domain = getDomainFast(index);
        TRACE('    - index=', index, 'dom=', domain__debug(domain));
        if (!domain) return;
        let newDomain = domain_removeValue(domain, 0);
        if (newDomain !== domain && updateDomain(index, newDomain)) return;
      }
      ml_eliminate(ml, offset, opSize);
      return;
    }

    // R is unresolved. check whether R can be determined
    ASSERT(domain_min(R) === 0 && domain_max(R) > 0, 'R is unresolved here', R);
    let allNonZero = true;
    let someAreZero = false;
    let someNonZero = false;
    for (let i = 0; i < argCount; ++i) {
      let index = readIndex(ml, offsetArgs + i * 2);
      let domain = getDomainFast(index);
      TRACE('    - index=', index, 'dom=', domain__debug(domain));

      // reflect isAll,
      // R=0 when at least one arg is zero
      // R>0 when all args have no zero

      if (domain_isZero(domain)) {
        TRACE(' - found a zero, breaking loop because R=0');
        someAreZero = true;
        break; // this permanently sets R to 0; no need to loop further
      } else if (domain_min(domain) === 0) {
        // arg has zero and non-zero values so R (at least) cant be set to 1 yet
        allNonZero = false;
      } else {
        someNonZero = true;
      }
    }

    if (someAreZero) {
      TRACE(' - At least one arg was zero so R=0 and constraint can be removed');
      let oR = R;
      R = domain_removeGtUnsafe(R, 0);
      if (R !== oR) updateDomain(indexR, R);
      ml_eliminate(ml, offset, opSize);
      return;
    }

    if (allNonZero) {
      TRACE(' - No arg had zero so R=1 and constraint can be removed');
      let oR = R;
      R = domain_removeValue(R, 0);
      if (R !== oR) updateDomain(indexR, R);
      ml_eliminate(ml, offset, opSize);
      return;
    }

    // remove all non-zero values from the list. this reduces their connection count and simplifies this isall
    if (someNonZero) {
      let removed = 0;
      for (let i = argCount - 1; i >= 0; --i) {
        let index = readIndex(ml, offsetArgs + i * 2);
        let domain = getDomainFast(index);
        TRACE('   - checking if index', index, '(domain', domain__debug(domain), ') contains no zero so we can remove it from this isall');
        if (domain_hasNoZero(domain)) {
          // now
          // - move all indexes bigger than the current back one position
          // - compile the new count back in
          // - compile a NOOP in the place of the last element
          TRACE('  - moving further domains one space forward (from ', i + 1, ' / ', argCount, ')');
          min_spliceArgSlow(ml, offsetArgs, argCount, i, true);
          --argCount;
          ++removed;
        }
      }

      ml_enc16(ml, offset + 1, argCount);
      // now "blank out" the space of eliminated constants, they should be at the end of the op
      let newOpSize = opSize - removed * 2;
      ml_compileJumpSafe(ml, offset + newOpSize, opSize - newOpSize);

      TRACE(' - Removed', removed, 'non-zero args from unsolved isall, has', argCount, 'left');
      TRACE(' - ml for this sum now:', ml.slice(offset, offset + opSize).join(' '));

      if (argCount === 1) _min_isAllMorphToXnor(ml, offset, argCount, offsetArgs, indexR);
      return;
    }

    if (argCount === 1) return _min_isAllMorphToXnor(ml, offset, argCount, offsetArgs, indexR);

    TRACE(' - not only jumps...');
    onlyJumps = false;
    pc = offset + opSize;
  }
  function _min_isAllMorphToXnor(ml, offset, argCount, offsetArgs, indexR) {
    // while this usually only happens when eliminating non-zeroes, there may be an artifact where a script
    // generated an isall with just one arg. kind of silly but whatever, right.
    TRACE(' - Only one arg remaining; morphing to a XNOR');
    ASSERT(argCount > 0, 'isall must have at least one arg in order to have enough space for the xnor morph');
    let index = readIndex(ml, offsetArgs);
    ml_cr2c2(ml, offset, argCount, ML_XNOR, indexR, index);
    varChanged = true; // the xnor may need optimization
  }

  function min_isNall(ml, offset) {
    let offsetCount = offset + 1;
    let argCount = ml_dec16(ml, offsetCount);
    let opSize = SIZEOF_C + argCount * 2 + 2;
    let offsetArgs = offset + SIZEOF_C;
    let offsetR = offset + opSize - 2;

    let indexR = readIndex(ml, offsetR);
    let R = getDomainFast(indexR);

    TRACE(' = min_isNall', argCount, 'x');
    TRACE('  - ml for this isNall:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  -', indexR, '= nall?(', Array.from(Array(argCount)).map((n, i) => readIndex(ml, offsetArgs + i * 2)), ')');
    TRACE('  -', domain__debug(R), '= nall?(', Array.from(Array(argCount)).map((n, i) => domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)))), ')');

    if (!R) return;

    if (domain_isZero(R)) {
      TRACE(' - R=0 so; !nall so; all so; we must remove zero from all args and eliminate constraint');
      for (let i = 0; i < argCount; ++i) {
        let index = readIndex(ml, offsetArgs + i * 2);
        let domain = getDomainFast(index);
        TRACE('    - index=', index, 'dom=', domain__debug(domain));
        if (!domain) return;
        let newDomain = domain_removeValue(domain, 0);
        if (newDomain !== domain && updateDomain(index, newDomain)) return;
      }
      ml_eliminate(ml, offset, opSize);
      return;
    }

    if (domain_hasNoZero(R)) {
      TRACE(' - R>0 so; nall. just morph and revisit');
      ml_enc8(ml, offset, ML_NALL);
      ml_compileJumpSafe(ml, offset + opSize - 2, 2); // difference between nall and isNall is the result var (16bit)
      return;
    }

    // R is unresolved. check whether R can be determined
    ASSERT(domain_min(R) === 0 && domain_max(R) > 0, 'R is unresolved here', R);
    let allNonZero = true;
    let someAreZero = false;
    for (let i = 0; i < argCount; ++i) {
      let index = readIndex(ml, offsetArgs + i * 2);
      let domain = getDomainFast(index);
      TRACE('    - index=', index, 'dom=', domain__debug(domain));

      // reflect isNall,
      // R=0 when all args have no zero
      // R>0 when at least one arg is zero

      if (domain_isZero(domain)) {
        TRACE(' - found a zero, breaking loop because R=0');
        someAreZero = true;
        break; // this permanently sets R to 0; no need to loop further
      } else if (domain_min(domain) === 0) {
        // arg has zero and non-zero values so R (at least) cant be set to 1 yet
        allNonZero = false;
      }
    }

    if (someAreZero) {
      TRACE(' - At least one arg was zero so R>=1 and constraint can be removed');
      let oR = R;
      R = domain_removeValue(R, 0);
      if (R !== oR) updateDomain(indexR, R, 'isnall, R>=1 because at least one var was zero');
      ml_eliminate(ml, offset, opSize);
    } else if (allNonZero) {
      TRACE(' - No arg had a zero so R=0 and constraint can be removed');
      let oR = R;
      R = domain_removeGtUnsafe(R, 0);
      if (R !== oR) updateDomain(indexR, R);
      ml_eliminate(ml, offset, opSize);
    } else {
      // TODO: prune all args here that are nonzero? is that worth it?

      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + opSize;
    }
  }

  function min_isSome(ml, offset) {
    let offsetCount = offset + 1;
    let argCount = ml_dec16(ml, offsetCount);
    let opSize = SIZEOF_C + argCount * 2 + 2;
    let offsetArgs = offset + SIZEOF_C;
    let offsetR = offset + opSize - 2;

    let indexR = readIndex(ml, offsetR);
    let R = getDomainFast(indexR);

    TRACE(' = min_isSome', argCount, 'x');
    TRACE('  - ml for this isSome:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  -', indexR, '= some?(', Array.from(Array(argCount)).map((n, i) => readIndex(ml, offsetArgs + i * 2)), ')');
    TRACE('  -', domain__debug(R), '= some?(', Array.from(Array(argCount)).map((n, i) => domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)))), ')');

    if (!R) return;

    if (domain_isZero(R)) {
      TRACE(' - R=0 so; !some so; none so; we must force zero to all args and eliminate constraint');
      for (let i = 0; i < argCount; ++i) {
        let index = readIndex(ml, offsetArgs + i * 2);
        let domain = getDomainFast(index);
        TRACE('    - index=', index, 'dom=', domain__debug(domain));
        if (!domain) return;
        let newDomain = domain_removeGtUnsafe(domain, 0);
        if (newDomain !== domain && updateDomain(index, newDomain)) return;
      }
      ml_eliminate(ml, offset, opSize);
      return;
    }

    if (domain_hasNoZero(R)) {
      TRACE(' - R>0 so; some. just morph and revisit');
      ml_enc8(ml, offset, ML_SOME);
      ml_compileJumpSafe(ml, offset + opSize - 2, 2); // difference between some and isSome is the result var (16bit)
      return;
    }

    // R is unresolved. check whether R can be determined
    ASSERT(domain_min(R) === 0 && domain_max(R) > 0, 'R is unresolved here', R);
    let someNonZero = false;
    let allZero = true;
    let someZero = false;
    for (let i = 0; i < argCount; ++i) {
      let index = readIndex(ml, offsetArgs + i * 2);
      let domain = getDomainFast(index);
      TRACE('    - index=', index, 'dom=', domain__debug(domain));

      // reflect isSome,
      // R=0 when all args are zero (already checked above)
      // R>0 when at least one arg is nonzero

      if (domain_hasNoZero(domain)) {
        TRACE(' - found a nonzero, breaking loop because R>0');
        someNonZero = true;
        break; // this permanently sets R to 0; no need to loop further
      } else if (domain_isZero(domain)) {
        someZero = true;
      } else {
        allZero = false;
      }
    }

    if (someNonZero) {
      TRACE(' - At least one arg was zero so R>=1 and constraint can be removed');
      let oR = R;
      R = domain_removeValue(R, 0);
      if (R !== oR) updateDomain(indexR, R, 'issome, R>=1 because at least one var was nonzero');
      ml_eliminate(ml, offset, opSize);
    } else if (allZero) {
      TRACE(' - All vars were zero so R=0 and constraint can be removed');
      let oR = R;
      R = domain_removeGtUnsafe(R, 0);
      if (R !== oR) updateDomain(indexR, R, 'issome, R>=1 because all vars were zero');
      ml_eliminate(ml, offset, opSize);
    } else if (someZero) {
      TRACE(' - Some vars were zero, removing them from the args');
      // force constants to the end
      ml_heapSort16bitInline(ml, pc + SIZEOF_C, argCount);
      // we know
      // - these args do not contain non-zero args
      // - all constants are moved to the back
      // - there is at least one constant 0
      // - not all args were 0
      // so we can move back the result var
      let argOffset = offsetArgs + argCount * 2 - 2;
      TRACE(' - offset:', offset, ', argCount:', argCount, ', args offset:', offsetArgs, ', first arg domain:', domain__debug(getDomain(readIndex(ml, offsetArgs))), ', last arg offset:', argOffset, ', last domain:', domain__debug(getDomain(readIndex(ml, argOffset))));
      TRACE(' - op before:', ml__debug(ml, offset, 1, problem));
      ASSERT(domain_isZero(getDomain(readIndex(ml, argOffset))), 'at least the last arg should be zero', domain__debug(getDomain(readIndex(ml, argOffset))));
      ASSERT(!domain_isZero(getDomain(readIndex(ml, offsetArgs))), 'the first arg should not be zero', domain__debug(getDomain(readIndex(ml, offsetArgs))));
      // search for the first non-zero arg
      let newArgCount = argCount;
      while (domain_isZero(getDomain(readIndex(ml, argOffset)))) {
        argOffset -= 2;
        --newArgCount;
      }
      TRACE(' - last non-zero arg is arg number', newArgCount, 'at', argOffset, ', index:', readIndex(ml, argOffset), ', domain:', domain__debug(getDomain(readIndex(ml, argOffset))));

      if (newArgCount === 1) {
        TRACE(' - there is one arg left, morph to XNOR');
        TRACE_MORPH('R = some?(A 0 0 ..)', 'R !^ A');
        let indexA = readIndex(ml, offsetArgs);
        ml_cr2c2(ml, offset, argCount, ML_XNOR, indexR, indexA);
      } else {
        TRACE(' - moving R to the first zero arg at offset', argOffset + 2, 'and compiling a jump for the rest');
        // copy the result var over the first zero arg
        ml_enc16(ml, offset + 1, newArgCount);
        ml_enc16(ml, argOffset + 2, indexR);
        ml_compileJumpSafe(ml, argOffset + 4, (argCount - newArgCount) * 2);
        ASSERT(ml_validateSkeleton(ml, 'min_isSome; pruning zeroes'));
      }
      TRACE(' - op after:', ml__debug(ml, offset, 1, problem));
    } else {
      // TODO: prune all args here that are zero? is that worth it?

      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + opSize;
    }
  }

  function min_isNone(ml, offset) {
    let offsetCount = offset + 1;
    let argCount = ml_dec16(ml, offsetCount);
    let opSize = SIZEOF_C + argCount * 2 + 2;
    let offsetArgs = offset + SIZEOF_C;
    let offsetR = offset + opSize - 2;

    let indexR = readIndex(ml, offsetR);
    let R = getDomainFast(indexR);

    TRACE(' = min_isNone', argCount, 'x');
    TRACE('  - ml for this isNone:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  -', indexR, '= none?(', Array.from(Array(argCount)).map((n, i) => readIndex(ml, offsetArgs + i * 2)), ')');
    TRACE('  -', domain__debug(R), '= none?(', Array.from(Array(argCount)).map((n, i) => domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)))), ')');

    if (!R) return;

    if (domain_hasNoZero(R)) {
      TRACE('    - R>=1 so set all args to zero and eliminate');
      for (let i = 0; i < argCount; ++i) {
        let index = readIndex(ml, offsetArgs + i * 2);
        let domain = getDomainFast(index);
        TRACE('    - index=', index, 'dom=', domain__debug(domain));
        if (!domain) return;
        let newDomain = domain_removeGtUnsafe(domain, 0);
        if (newDomain !== domain && updateDomain(index, newDomain)) return;
      }
      ml_eliminate(ml, offset, opSize);
      return;
    }

    if (domain_isZero(R)) {
      TRACE(' - R=0 so this is a SOME. just morph and revisit');
      TRACE_MORPH('0 = none?(A B C ...)', 'some(A B C ...)');
      ml_enc8(ml, offset, ML_SOME);
      ml_compileJumpSafe(ml, offset + opSize - 2, 2); // difference between some and isNone is the result var (16bit)
      return;
    }

    // R has a zero or is zero, determine whether there is any nonzero arg, or whether they are all zero
    let nonZero = false;
    let allZero = true;
    for (let i = 0; i < argCount; ++i) {
      let index = readIndex(ml, offsetArgs + i * 2);
      let domain = getDomainFast(index);
      TRACE('    - index=', index, 'dom=', domain__debug(domain));

      // reflect isNone,
      // R=0 when at least one arg is nonzero
      // R>0 when all args are zero

      if (domain_hasNoZero(domain)) {
        nonZero = true;
        break;
      }
      if (!domain_isZero(domain)) {
        allZero = false;
      }
    }

    if (nonZero) {
      TRACE(' - at least one arg had no zero so R=0, eliminate constraint');
      let oR = R;
      R = domain_removeGtUnsafe(R, 0);
      if (R !== oR) updateDomain(indexR, R, 'isnone R=0 because an arg had no zero');
      ml_eliminate(ml, offset, opSize);
    } else if (allZero) {
      TRACE(' - isnone, all args are 0 so R>=1, remove constraint');
      let oR = R;
      R = domain_removeValue(R, 0);
      if (R !== oR) updateDomain(indexR, R, 'isnone R>=1 because all args were zero');
      ml_eliminate(ml, offset, opSize);
    } else {
      // TODO: prune all args here that are zero? is that worth it?

      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + SIZEOF_C + argCount * 2 + 2;
    }
  }

  function min_diff(ml, offset) {
    let argCount = ml_dec16(ml, offset + 1);
    let offsetArgs = offset + SIZEOF_C;
    let opSize = SIZEOF_C + argCount * 2;

    TRACE(' = min_diff', argCount, 'x');
    TRACE('  - ml for this diff:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  - indexes:', Array.from(Array(argCount)).map((n, i) => readIndex(ml, offsetArgs + i * 2)).join(', '));
    TRACE('  - domains:', Array.from(Array(argCount)).map((n, i) => domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)))).join(', '));

    ASSERT(argCount, 'should have at least one arg or be eliminated');
    if (!argCount) return setEmpty(-1, 'diff without args is probably a bug');

    let countStart = argCount;

    // a diff is basically a pyramid of neq's; one for each unique pair of the set
    // we loop back to front because we're splicing out vars while looping
    for (let i = argCount - 1; i >= 0; --i) {
      let indexA = readIndex(ml, offsetArgs + i * 2);
      let A = getDomainFast(indexA);
      TRACE('  - loop i=', i, 'index=', indexA, 'domain=', domain__debug(A));
      if (!A) return;

      let v = domain_getValue(A);
      if (v >= 0) {
        TRACE('   - solved, so removing', v, 'from all other domains and index', indexA, 'from the constraint');
        for (let j = 0; j < argCount; ++j) { // gotta loop through all args. args wont be removed in this loop.
          if (j !== i) {
            let indexB = readIndex(ml, offsetArgs + j * 2);
            let oB = getDomainFast(indexB);
            TRACE('    - loop j=', j, 'index=', indexB, 'domain=', domain__debug(oB));
            if (indexA === indexB) return updateDomain(indexA, domain_createEmpty(), 'diff had this var twice, x!=x is a falsum'); // edge case

            let B = domain_removeValue(oB, v);
            if (B !== oB && updateDomain(indexB, B, 'diff arg')) return;
          }
        }
        // so none of the other args have v and none of them ended up empty

        // now
        // - move all indexes bigger than the current back one position
        // - compile the new count back in
        // - compile a NOOP in the place of the last element
        TRACE('  - moving further domains one space forward (from ', i + 1, ' / ', argCount, ')', i + 1 < argCount);
        min_spliceArgSlow(ml, offsetArgs, argCount, i, true); // move R as well
        --argCount;
      }
    }

    if (argCount <= 1) {
      TRACE(' - Count is', argCount, '; eliminating constraint');
      ASSERT(argCount >= 0, 'cant be negative');
      ml_eliminate(ml, offset, opSize);
    } else if (argCount !== countStart) {
      TRACE('  - recompiling new count (', argCount, ')');
      ml_enc16(ml, offset + 1, argCount);
      TRACE('  - compiling noop into empty spots'); // this hasnt happened yet
      ml_compileJumpSafe(ml, offsetArgs + argCount * 2, (countStart - argCount) * 2);
      // need to restart op because the skip may have clobbered the next op offset
    } else if (argCount === 2 && min_diff_2(ml, offset)) {
      // do nothing. min_diff_2 has already done something.
    } else {
      TRACE(' - not only jumps...', opSize);
      onlyJumps = false;
      pc = offset + opSize;
    }
  }

  function min_sum_2(ml, sumOffset) {
    let offsetA = sumOffset + OFFSET_C_A;
    let offsetB = sumOffset + OFFSET_C_B;
    let offsetR = sumOffset + OFFSET_C_R;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let indexR = readIndex(ml, offsetR);

    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);
    let R = getDomainFast(indexR);

    TRACE(' = min_sum_2', indexR, '=', indexA, '+', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '+', domain__debug(B));
    if (!A || !B || !R) return false;

    ASSERT(ml_dec8(ml, sumOffset) === ML_SUM, 'should be a sum with 2 args');
    ASSERT(ml_dec16(ml, sumOffset + 1) === 2, 'should have 2 args');

    // note: A + B = C   ==>   <loA + loB, hiA + hiB>
    // but:  A - B = C   ==>   <loA - hiB, hiA - loB>   (so the lo/hi of B gets swapped!)
    // keep in mind that any number oob <sub,sup> gets pruned in either case, this makes
    // plus and minus are not perfect (counter-intuitively): `[0, 2] - [0, 4] = [0, 2]`

    let ooA = A;
    let ooB = B;
    let ooR = R;

    let oA, oB, oR;
    let loops = 0;
    do {
      ++loops;
      TRACE(' - plus propagation step...', loops, domain__debug(R), '=', domain__debug(A), '+', domain__debug(B));
      oA = A;
      oB = B;
      oR = R;

      R = domain_intersection(R, domain_plus(A, B));
      A = domain_intersection(A, domain_minus(R, B));
      B = domain_intersection(B, domain_minus(R, A));
    } while (A !== oA || B !== oB || R !== oR);

    TRACE(' ->', 'R:', domain__debug(R), '= A:', domain__debug(A), '+ B:', domain__debug(B));

    if (loops > 1) {
      if (A !== ooA) updateDomain(indexA, A, 'plus A');
      if (B !== ooB) updateDomain(indexB, B, 'plus B');
      if (R !== ooR) updateDomain(indexR, R, 'plus R');
      if (!A || !B || !R) return false;
    }

    let vA = domain_getValue(A);
    let vB = domain_getValue(B);
    let vR = domain_getValue(R);

    ASSERT(((vA >= 0) + (vB >= 0) + (vR >= 0)) !== 2, 'if two vars are solved the third should be solved as well');

    if (vA >= 0 && vB >= 0) { // so vR>=0 as well
      TRACE(' - All args are solved so removing constraint');
      ASSERT(vR >= 0, 'if two are solved then all three must be solved');
      ml_eliminate(ml, sumOffset, SIZEOF_CR_2);
      return true;
    }

    if (vA >= 0) {
      ASSERT(vB < 0 && vR < 0);
      if (min_plusWithSolvedArg(sumOffset, indexB, indexA, indexR, A, B, R, vA, 'A', 'B')) {
        return true;
      }
    }

    if (vB >= 0) {
      ASSERT(vA < 0 && vR < 0);
      if (min_plusWithSolvedArg(sumOffset, indexA, indexB, indexR, B, A, R, vB, 'B', 'A')) {
        return true;
      }
    }
    //
    //TRACE(' - not only jumps');
    //onlyJumps = false;
    //pc = sumOffset + SIZEOF_CR_2;
    return false;
  }
  function intersectAndAlias(indexFrom, indexTo, F, T) {
    TRACE(' - intersectAndAlias; from index:', indexFrom, ', to index:', indexTo, ', F:', domain__debug(F), ', T:', domain__debug(T), ', FT:', domain__debug(domain_intersection(F, T)));
    ASSERT(typeof indexFrom === 'number' && indexFrom >= 0, 'indexfrom check');
    ASSERT(typeof indexTo === 'number' && indexTo >= 0, 'indexto check');
    ASSERT(F && T, 'should not receive empty domains... catch this at caller');
    ASSERT_NORDOM(F);
    ASSERT_NORDOM(T);
    ASSERT(getDomain(indexFrom) === F, 'F should match domain');
    ASSERT(getDomain(indexTo) === T, 'T should match domain');

    let FT = domain_intersection(F, T);
    if (F !== T) {
      updateDomain(indexTo, FT, 'intersectAndAlias');
    }
    if (FT && !domain_isSolved(F)) addAlias(indexFrom, indexTo);

    return FT;
  }
  function min_plusWithSolvedArg(sumOffset, indexY, indexX, indexR, X, Y, R, vX, nameX, nameY) {
    TRACE(' - min_plusWithSolvedArg', nameX, nameY, domain__debug(R), '=', domain__debug(X), '+', domain__debug(Y));
    ASSERT(vX >= 0, 'caller should assert that X is solved');
    ASSERT(domain_isSolved(Y) + domain_isSolved(R) === 0, 'caller should assert that only one of the three is solved');

    if (vX === 0) {
      TRACE(' -', nameX, '= 0, so R =', nameY, '+ 0, so R ==', nameY, ', morphing op to eq');
      // morph R=0+Y to R==Y

      intersectAndAlias(indexR, indexY, R, Y);
      ml_eliminate(ml, sumOffset, SIZEOF_CR_2);
      varChanged = true;
      return true;
    }

    // try to morph R=x+Y to x=R==?Y when R has two values and Y is [0, 1] (because it cant be solved, so not 0 nor 1)
    // R    = A + B           ->        B    = A ==? R    (when B is [01] and A is solved)
    // [01] = 1 + [01]        ->        [01] = 1 !=? [0 1]
    // [12] = 1 + [01]        ->        [01] = 1 !=? [1 2]
    // [10 11] = 10 + [01]    ->        [01] = 10 !=? [10 11]
    // rationale; B=bool means the solved value in A can only be A or
    // A+1. when B=1 then R=A+1 and diff. when B=0 then R=A and eq.
    // this only works when vX==max(R) because its either +0 or +1
    if (domain_isBool(Y) && domain_size(R) === 2 && domain_min(R) === vX) {
      TRACE(' - R = X + Y   ->   Y = X ==? R    (Y is [01] and X is solved to', vX, ')');
      TRACE('   - R =', vX, '+', nameY, 'to', nameY, '=', vX, domain_max(R) === vX ? '==?' : '!=? R');
      TRACE('   -', domain__debug(R), '=', vX, '+', domain__debug(Y), 'to ', domain__debug(Y), '=', vX, '==?', domain__debug(R));
      TRACE(' - morphing R=A+B to B=A!=?R with A solved and B=[01] and size(R)=2');
      ml_cr2cr2(ml, sumOffset, 2, ML_ISDIFF, indexR, indexX, indexY);
      varChanged = true;
      return true;
    }

    TRACE('   - min_plusWithSolvedArg did nothing');
    return false;
  }

  function min_minus(ml, offset) {
    let offsetA = offset + 1;
    let offsetB = offset + 3;
    let offsetR = offset + 5;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let indexR = readIndex(ml, offsetR);

    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);
    let R = getDomainFast(indexR);

    TRACE(' = min_minus', indexR, '=', indexA, '-', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '-', domain__debug(B));
    if (!A || !B || !R) return;

    // C = A - B   -> A = B + C, B = C - A
    // note: A - B = C   ==>   <loA - hiB, hiA - loB>
    // but:  A + B = C   ==>   <loA + loB, hiA + hiB>   (so the lo/hi of B gets swapped!)
    // keep in mind that any number oob <sub,sup> gets trimmed in either case.
    // this trimming may affect "valid" numbers in the other domains so that needs back-propagation.

    let ooA = A;
    let ooB = B;
    let ooR = R;

    let oA, oB, oR;
    let loops = 0;
    do {
      ++loops;
      TRACE(' - minus propagation step...', loops, domain__debug(R), '=', domain__debug(A), '+', domain__debug(B));
      oA = A;
      oB = B;
      oR = R;

      R = domain_intersection(R, domain_minus(A, B));
      A = domain_intersection(A, domain_plus(R, B));
      B = domain_intersection(B, domain_minus(A, R));
    } while (A !== oA || B !== oB || R !== oR);

    TRACE(' ->', 'A:', domain__debug(A), 'B:', domain__debug(B), 'R:', domain__debug(R));

    if (loops > 1) {
      if (A !== ooA) updateDomain(indexA, A, 'minus A');
      if (B !== ooB) updateDomain(indexB, B, 'minus B');
      if (R !== ooR) updateDomain(indexR, R, 'minus R');
      if (!A || !B || !R) return;
    }

    ASSERT((domain_isSolved(A) + domain_isSolved(B) + domain_isSolved(R)) !== 2, 'if two vars are solved the third should be solved as well');

    if (domain_isSolved(R) && domain_isSolved(A)) { // minR==maxR&&minA==maxA
      ASSERT(domain_isSolved(B), 'if two are solved then all three must be solved');
      ml_eliminate(ml, offset, SIZEOF_VVV);
    } else if (domain_getValue(A) === 0) { // maxA==0
      TRACE(' - A=0 so B==R, aliasing R to B, eliminating constraint');
      intersectAndAlias(indexR, indexB, R, B);
      ml_eliminate(ml, offset, SIZEOF_VVV);
      varChanged = true;
    } else if (domain_getValue(B) === 0) { // maxB==0
      TRACE(' - B=0 so A==R, aliasing R to A, eliminating constraint');
      intersectAndAlias(indexR, indexA, R, A);
      ml_eliminate(ml, offset, SIZEOF_VVV);
      varChanged = true;
    } else {
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + SIZEOF_VVV;
    }
  }

  function min_product_2(ml, offset) {
    let offsetA = offset + OFFSET_C_A;
    let offsetB = offset + OFFSET_C_B;
    let offsetR = offset + OFFSET_C_R;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let indexR = readIndex(ml, offsetR);

    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);
    let R = getDomainFast(indexR);

    TRACE(' = min_product_2', indexR, '=', indexA, '*', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '*', domain__debug(B));
    if (!A || !B || !R) {
      TRACE(' - found empty domain, rejecting');
      return true;
    }

    // C = A * B, B = C / A, A = C / B
    // note: A * B = C   ==>   <loA * loB, hiA * hiB>
    // but:  A / B = C   ==>   <loA / hiB, hiA / loB> and has rounding/div-by-zero issues! instead use "inv-mul" tactic
    // keep in mind that any number oob <sub,sup> gets pruned in either case. x/0=0
    // when dividing "do the opposite" of integer multiplication. 5/4=[] because there is no int x st 4*x=5
    // only outer bounds are evaluated here...

    let ooA = A;
    let ooB = B;
    let ooR = R;

    let oA, oB, oR;
    let loops = 0;
    do {
      ++loops;
      TRACE(' - mul propagation step...', loops, domain__debug(R), '=', domain__debug(A), '*', domain__debug(B));
      oA = A;
      oB = B;
      oR = R;

      R = domain_intersection(R, domain_mul(A, B));
      A = domain_intersection(A, domain_invMul(R, B));
      B = domain_intersection(B, domain_invMul(R, A));
    } while (A !== oA || B !== oB || R !== oR);

    TRACE(' ->', 'A:', domain__debug(A), 'B:', domain__debug(B), 'R:', domain__debug(R));

    if (loops > 1) {
      if (A !== ooA) updateDomain(indexA, A, 'mul A');
      if (B !== ooB) updateDomain(indexB, B, 'mul B');
      if (R !== ooR) updateDomain(indexR, R, 'mul R');
      if (!A || !B || !R) {
        TRACE(' - found empty domain, rejecting');
        return true;
      }
    }

    ASSERT((domain_isSolved(A) + domain_isSolved(B) + domain_isSolved(R)) !== 2 || domain_getValue(R) === 0, 'if two vars are solved the third should be solved as well unless R is 0');

    if (domain_isSolved(R) && domain_isSolved(A)) {
      TRACE(' - A B R all solved, eliminating constraint; ABR:', domain__debug(A), domain__debug(B), domain__debug(R));
      ASSERT(domain_isZero(R) || domain_isSolved(B), 'if two are solved then all three must be solved or R is zero');
      ml_eliminate(ml, offset, SIZEOF_CR_2, true);
      return true;
    }

    TRACE('   - min_product_2 did not do anything');
    return false;
  }

  function min_div(ml, offset) {
    let offsetA = offset + 1;
    let offsetB = offset + 3;
    let offsetR = offset + 5;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let indexR = readIndex(ml, offsetR);

    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);
    let R = getDomainFast(indexR);

    TRACE(' = min_div', indexR, '=', indexA, '*', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '/', domain__debug(B));
    if (!A || !B || !R) return;

    // R = A / B, A = R * B, B = A / R
    // note:  A / B = C   ==>   <loA / hiB, hiA / loB> and has rounding/div-by-zero issues!
    // but: A * B = C   ==>   <loA * loB, hiA * hiB> use "inv-div" tactic
    // basically remove any value from the domains that can not lead to a valid integer result A/B=C

    TRACE(' - div propagation step...', domain__debug(R), '=', domain__debug(A), '/', domain__debug(B));
    let oR = R;
    R = domain_intersection(R, domain_divby(A, B));
    TRACE(' ->', 'R:', domain__debug(R), '=', 'A:', domain__debug(A), '/', 'B:', domain__debug(B));

    if (R !== oR) updateDomain(indexR, R, 'div R');
    if (!A || !B || !R) return;

    TRACE(' - domains;', domain__debug(R), '=', domain__debug(A), '/', domain__debug(B));
    if (domain_isSolved(B) && domain_isSolved(A)) {
      ASSERT(domain_isSolved(R), 'if A and B are solved then R should be solved');
      ml_eliminate(ml, offset, SIZEOF_VVV);
    } else {
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + SIZEOF_VVV;
    }
  }

  function min_isSame(ml, offset) {
    let argCount = ml_dec16(ml, offset + 1);

    TRACE(' = min_isSame, arg count:', argCount);

    if (argCount !== 2) {
      TRACE(' - argcount !== 2 so bailing for now');

      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + SIZEOF_C + argCount * 2 + 2;
      return;
    }

    let offsetA = offset + OFFSET_C_A;
    let offsetB = offset + OFFSET_C_B;
    let offsetR = offset + OFFSET_C_R;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let indexR = readIndex(ml, offsetR);

    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);
    let R = getDomainFast(indexR);

    TRACE(' - min_isSame', indexR, '=', indexA, '==?', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '==?', domain__debug(B));
    if (!A || !B || !R) return;

    if (indexA === indexB) {
      TRACE(' - indexA == indexB so forcing R to 1 and removing constraint');
      let oR = R;
      R = domain_removeValue(R, 0);
      if (R !== oR) updateDomain(indexR, R, 'issame R: A!=B');
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_eliminate(ml, offset, SIZEOF_CR_2);
      return;
    }

    let vA = domain_getValue(A);
    let vB = domain_getValue(B);

    if (vA >= 0 && vB >= 0) {
      TRACE(' - A and B are solved so we can determine R and eliminate the constraint');

      let oR = R;
      if (A === B) {
        R = domain_removeValue(R, 0);
        if (R !== oR) updateDomain(indexR, R, 'issame R: A==B');
      } else {
        R = domain_intersectionValue(R, 0);
        if (R !== oR) updateDomain(indexR, R, 'issame R: A!=B');
      }

      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_eliminate(ml, offset, SIZEOF_CR_2);
      return;
    }

    // A and B arent both solved. check R
    if (domain_isZero(R)) {
      TRACE(' ! R=0 while A or B isnt solved, changing issame to diff and revisiting');
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_cr2c2(ml, offset, 2, ML_DIFF, indexA, indexB);
      varChanged = true;
      return;
    }

    if (domain_hasNoZero(R)) {
      TRACE(' ! R>=1 while A or B isnt solved, aliasing A to B, eliminating constraint');
      intersectAndAlias(indexA, indexB, A, B);
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_eliminate(ml, offset, SIZEOF_CR_2);
      varChanged = true;
      return;
    }

    if (indexA === indexB) {
      TRACE(' ! index A === index B so R should be truthy and we can eliminate the constraint');
      let oR = R;
      R = domain_removeValue(R, 0);
      if (R !== oR) updateDomain(indexR, R, 'issame R: A==B');
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_eliminate(ml, offset, SIZEOF_CR_2);
      return;
    }

    if (!domain_intersection(A, B)) {
      TRACE(' - no overlap between', indexA, 'and', indexB, ' (', domain__debug(A), domain__debug(B), ') so R becomes 0 and constraint is removed');
      let oR = R;
      R = domain_removeGtUnsafe(R, 0);
      if (R !== oR) updateDomain(indexR, R, 'issame; no overlap A B so R=0');
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_eliminate(ml, offset, SIZEOF_CR_2);
      return;
    }

    // there are some bool-domain-specific tricks we can apply
    // TODO: shouldnt these also confirm that A and/or B are actually solved? and not -1
    if (domain_isBool(R)) {
      // if A=0|1, B=[0 1], R=[0 1] we can recompile this to DIFF or SAME
      if (vA >= 0 && vA <= 1 && domain_isBool(B)) {
        TRACE(' ! [01]=0|1==?[01] so morphing to n/eq and revisiting');
        ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
        // - A=0: 0==A=1, 1==A=0: B!=R
        // - A=1: 0==A=0, 1==A=1: B==R
        if (vA === 0) {
          TRACE('   - morphing constraint to diff');
          ml_cr2c2(ml, offset, 2, ML_DIFF, indexB, indexR);
        } else {
          TRACE('   - aliasing R to B, eliminating constraint');
          intersectAndAlias(indexR, indexB, R, B);
          ml_eliminate(ml, offset, SIZEOF_CR_2);
        }
        varChanged = true;
        return;
      }

      // if A=[0 1], B=0|1, R=[0 1] we can recompile this to DIFF or SAME
      if (vB >= 0 && vB <= 1 && domain_isBool(A)) {
        TRACE(' ! [01]=[01]==?0|1 so morphing to n/eq and revisiting');
        ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
        // - B=0: 0==B=1, 1==B=0: A!=R
        // - B=1: 0==B=0, 1==B=1: A==R
        if (vB === 0) {
          TRACE('   - morphing constraint to diff');
          ml_cr2c2(ml, offset, 2, ML_DIFF, indexA, indexR);
        } else {
          TRACE('   - aliasing R to A, eliminating constraint');
          intersectAndAlias(indexR, indexA, R, A);
          ml_eliminate(ml, offset, SIZEOF_CR_2);
        }
        varChanged = true;
        return;
      }

      // note: cant do XNOR trick here because that only works on BOOLY vars
    }

    if (vA === 0) {
      // this means R^B
      TRACE(' ! A=0 so R^B, morphing to xor');
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_cr2c2(ml, offset, 2, ML_XOR, indexR, indexB);
      varChanged = true;
      return;
    }

    if (vB === 0) {
      // this means R^A
      TRACE(' ! B=0 so R^A, morphing to xor');
      ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
      ml_cr2c2(ml, offset, 2, ML_XOR, indexR, indexA);
      varChanged = true;
      return;
    }

    TRACE(' ->', domain__debug(R), '=', domain__debug(A), '==?', domain__debug(B));
    ASSERT(domain_min(R) === 0 && domain_max(R) > 0, 'R should be a booly at this point', domain__debug(R));

    TRACE(' - not only jumps...');
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'arg count should be 2 here');
    onlyJumps = false;
    pc = offset + SIZEOF_CR_2;
  }

  function min_isDiff(ml, offset) {
    let argCount = ml_dec16(ml, offset + 1);

    TRACE(' = min_isDiff; argCount=', argCount);

    if (argCount !== 2) {
      TRACE(' - count != 2, bailing for now');

      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + SIZEOF_C + argCount * 2 + 2;
      return;
    }

    let offsetA = offset + OFFSET_C_A;
    let offsetB = offset + OFFSET_C_B;
    let offsetR = offset + OFFSET_C_R;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let indexR = readIndex(ml, offsetR);

    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);
    let R = getDomainFast(indexR);

    TRACE(' = min_isDiff', indexR, '=', indexA, '!=?', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '!=?', domain__debug(B));
    if (!A || !B || !R) return;

    if (domain_isSolved(A) && domain_isSolved(B)) {
      TRACE(' - A and B are solved so we can determine R');
      let oR = R;
      if (A === B) {
        R = domain_removeGtUnsafe(R, 0);
        if (R !== oR) updateDomain(indexR, R, 'isdiff R; A==B');
      } else {
        R = domain_removeValue(R, 0);
        if (R !== oR) updateDomain(indexR, R, 'isdiff R; A!=B');
      }
      ml_eliminate(ml, offset, SIZEOF_CR_2);
      return;
    }

    // R should be 0 if A==B. R should be >0 if A!==B
    if (domain_isZero(R)) {
      TRACE(' ! R=0, aliasing A to B, eliminating constraint');
      intersectAndAlias(indexA, indexB, A, B);
      ml_eliminate(ml, offset, SIZEOF_CR_2);
      varChanged = true;
      return;
    }

    if (domain_hasNoZero(R)) {
      TRACE(' ! R>0, changing isdiff to diff and revisiting');
      ml_cr2c2(ml, offset, 2, ML_DIFF, indexA, indexB);
      varChanged = true;
      return;
    }

    TRACE(' ->', domain__debug(R), '=', domain__debug(A), '!=?', domain__debug(B));
    TRACE(' - not only jumps...');
    ASSERT(domain_min(R) === 0 && domain_max(R) >= 1, 'R should be boolable at this point');
    onlyJumps = false;
    pc = offset + SIZEOF_CR_2;
  }

  function min_isLt(ml, offset) {
    let offsetA = offset + 1;
    let offsetB = offset + 3;
    let offsetR = offset + 5;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let indexR = readIndex(ml, offsetR);

    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);
    let R = getDomainFast(indexR);

    TRACE(' = min_isLt', indexR, '=', indexA, '<?', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '<?', domain__debug(B));
    if (!A || !B || !R) return;

    let oR = R;
    if (!domain_isSolved(R)) {
      if (domain_max(A) < domain_min(B)) R = domain_removeValue(R, 0);
      else if (domain_min(A) >= domain_max(B)) R = domain_removeGtUnsafe(R, 0);
    }
    if (R !== oR && !updateDomain(indexR, R, 'islt; solving R because A < B or A >= B')) return;

    // if R is solved replace this isLt with an lt or "gt" and repeat.
    // the appropriate op can then prune A and B accordingly.
    // in this context, the inverse for lt is an lte with swapped args

    if (domain_isZero(R)) {
      TRACE(' ! result var solved to 0 so compiling an lte with swapped args in its place', indexB, 'and', indexA);
      ml_vvv2c2(ml, offset, ML_LTE, indexB, indexA);
      varChanged = true;
      return;
    }

    if (domain_hasNoZero(R)) {
      TRACE(' ! result var solved to 1 so compiling an lt in its place for', indexA, 'and', indexB);
      ml_vvv2c2(ml, offset, ML_LT, indexA, indexB);
      varChanged = true;
      return;
    }

    if (domain_isZero(A)) {
      TRACE(' - A=0 ! R=0<?B [01]=0<?[0 10] so if B=0 then R=0 and otherwise R=1 so xnor');
      TRACE_MORPH('R=0<?B', 'R!^B');
      ml_vvv2c2(ml, offset, ML_XNOR, indexR, indexB);
      varChanged = true;
      return;
    }

    if (domain_isZero(B)) {
      TRACE(' - B=0 ! so thats just false');
      TRACE_MORPH('R=A<?0', 'R=0');
      ml_eliminate(ml, offset, SIZEOF_VVV);
      return;
    }

    TRACE(' - not only jumps...');
    onlyJumps = false;
    pc = offset + SIZEOF_VVV;
  }

  function min_isLte(ml, offset) {
    let offsetA = offset + 1;
    let offsetB = offset + 3;
    let offsetR = offset + 5;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let indexR = readIndex(ml, offsetR);

    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);
    let R = getDomainFast(indexR);

    TRACE(' = min_isLte', indexR, '=', indexA, '<=?', indexB, '   ->   ', domain__debug(R), '=', domain__debug(A), '<=?', domain__debug(B));
    if (!A || !B || !R) return;

    let oR = R;
    TRACE(' - max(A) <= min(B)?', domain_max(A), '<=', domain_min(B));
    TRACE(' - min(A) > max(B)?', domain_min(A), '>', domain_max(B));
    // if R isn't resolved you can't really update A or B. so we don't.
    if (domain_max(A) <= domain_min(B)) R = domain_removeValue(R, 0);
    else if (domain_min(A) > domain_max(B)) R = domain_removeGtUnsafe(R, 0);
    if (R !== oR) {
      TRACE(' - updated R to', domain__debug(R));
      if (updateDomain(indexR, R, 'islte; solving R because A and B are solved')) return;
    }

    let falsyR = domain_isZero(R);
    let truthyR = falsyR ? false : domain_hasNoZero(R);

    // if R is resolved replace this isLte with an lte or "gte" and repeat.
    // the appropriate op can then prune A and B accordingly.
    // in this context, the logical inverse for lte is an lt with swapped args

    if (falsyR) {
      TRACE(' ! result var solved to 0 so compiling an lt with swapped args in its place', indexB, 'and', indexA);
      ml_vvv2c2(ml, offset, ML_LT, indexB, indexA);
      varChanged = true;
      return;
    }

    if (truthyR) {
      TRACE(' ! result var solved to 1 so compiling an lte in its place', indexA, 'and', indexB);
      ml_vvv2c2(ml, offset, ML_LTE, indexA, indexB);
      varChanged = true;
      return;
    }

    // TODO: C=A<=?B   ->   [01] = [11] <=? [0 n]   ->   B !^ C

    if (domain_isBool(R) && domain_max(A) <= 1 && domain_max(B) <= 1) {
      TRACE(' - R is bool and A and B are bool-bound so checking bool specific cases');
      ASSERT(!domain_isZero(A) || !domain_isBool(B), 'this case should be caught by max<min checks above');

      if (domain_isBool(A) && domain_isZero(B)) {
        TRACE_MORPH('[01] = [01] <=? 0', 'A != R');
        ml_vvv2c2(ml, offset, ML_DIFF, indexA, indexR);
        varChanged = true;
        return;
      }
      if (domain_isBool(A) && B === domain_createValue(1)) {
        TRACE_MORPH('[01] = [01] <=? 1', 'A == R');
        intersectAndAlias(indexA, indexR, A, R);
        ml_eliminate(ml, offset, SIZEOF_VVV);
        varChanged = true;
        return;
      }
      if (domain_isBool(B) && A === domain_createValue(1)) {
        TRACE_MORPH('[01] = 1 <=? [01]', 'B == R');
        intersectAndAlias(indexB, indexR, B, R);
        ml_eliminate(ml, offset, SIZEOF_VVV);
        varChanged = true;
        return;
      }
    }

    TRACE(' - not only jumps...');
    onlyJumps = false;
    pc = offset + SIZEOF_VVV;
  }

  function min_sum(ml, offset) {
    let offsetCount = offset + 1;
    let argCount = ml_dec16(ml, offsetCount);

    if (argCount === 2) {
      if (min_sum_2(ml, offset)) return; // TOFIX: merge with this function...?
    }

    let opSize = SIZEOF_C + argCount * 2 + 2;
    let offsetArgs = offset + SIZEOF_C;
    let offsetR = offset + opSize - 2;

    let indexR = readIndex(ml, offsetR);
    let R = getDomainFast(indexR);

    TRACE(' = min_sum', argCount, 'x');
    TRACE('  - ml for this sum:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  - indexes:', indexR, '= sum(', Array.from(Array(argCount)).map((n, i) => readIndex(ml, offsetArgs + i * 2)).join(', '), ')');
    TRACE('  - domains:', domain__debug(R), '= sum(', Array.from(Array(argCount)).map((n, i) => domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)))).join(', '), ')');

    if (!R) return;

    // a sum is basically a pyramid of plusses; (A+B)+(C+D) etc
    // we loop back to front because we're splicing out vars while looping

    // replace all constants by one constant
    // prune the result var by intersecting it with the sum of the actual args
    // in limited cases we can prune some of the arg values if the result forces
    // that (if the result is max 10 then inputs can be pruned of any value > 10)
    // we cant really do anything else

    TRACE(' - first loop to get the sum of the args and constants');
    let sum = domain_createValue(0);
    let constants = 0;
    let constantSum = 0;
    for (let i = 0; i < argCount; ++i) {
      let argOffset = offsetArgs + i * 2;
      let index = readIndex(ml, argOffset);
      let domain = getDomainFast(index);
      TRACE('    - i=', i, ', offset=', argOffset, ', index=', index, 'dom=', domain__debug(domain), ', constants before:', constants, 'sum of constant before:', constantSum);
      let v = domain_getValue(domain);
      if (v >= 0) {
        TRACE('      - this is a constant! value =', v);
        ++constants;
        constantSum += v;
      }
      sum = domain_plus(sum, domain);
    }

    TRACE(' - total sum=', domain__debug(sum), ', constantSum=', constantSum, 'with', constants, 'constants. applying to R', domain__debug(R), '=>', domain__debug(domain_intersection(sum, R)));

    let oR = R;

    if (constants === argCount) { // bit of an edge case, though it can happen after multiple passes
      TRACE(' - all sum args are constants so R must simply eq their sum, eliminating constraint');
      R = domain_intersectionValue(R, constantSum);
      if (R !== oR) updateDomain(indexR, R, 'setting R to sum of constants');
      ml_eliminate(ml, offset, opSize);
      return;
    }

    R = domain_intersection(sum, R);
    TRACE(' - Updated R from', domain__debug(oR), 'to', domain__debug(R));
    if (R !== oR && updateDomain(indexR, R, 'sum; updating R with outer bounds of its args;')) return;

    ASSERT(constantSum <= domain_max(R), 'the sum of constants should not exceed R', constantSum);

    // get R without constants to apply to var args
    let subR = constantSum ? domain_minus(R, domain_createValue(constantSum)) : R;
    ASSERT(subR, 'R-constants should not be empty', constantSum);

    TRACE(' - Now back propagating R to the args. R-constants:', domain__debug(subR));

    // have to count constants and sum again because if a var occurs twice and this
    // updates it to a constant, the second one would otherwise be missed as old.
    constants = 0;
    constantSum = 0;

    // we can only trim bounds, not a full intersection (!)
    // note that trimming may lead to more constants so dont eliminate them here (KIS)
    let minSR = domain_min(subR);
    let maxSR = domain_max(subR);
    let varIndex1 = -1; // track non-constants for quick optimizations for one or two vars
    let varIndex2 = -1;
    for (let i = 0; i < argCount; ++i) {
      let index = readIndex(ml, offsetArgs + i * 2);
      let domain = getDomainFast(index);
      TRACE('    - i=', i, ', index=', index, 'dom=', domain__debug(domain));
      let v = domain_getValue(domain);
      if (v >= 0) {
        TRACE('      - old constant (or var that occurs twice and is now a new constant)', v);
        ++constants;
        constantSum += v;
      } else {
        // so the idea is that any value in an arg that could not even appear in R if all other args
        // were zero, is a value that cant ever yield a solution. those are the values we trim here.
        // this process takes constants in account (hence subR) because they don't have a choice.
        let newDomain = domain_removeLtUnsafe(domain, minSR);
        newDomain = domain_removeGtUnsafe(domain, maxSR);
        if (newDomain !== domain && updateDomain(index, newDomain, 'plus arg; trim invalid values')) return;

        v = domain_getValue(newDomain);
        if (v >= 0) {
          TRACE('      - new constant', v);
          // arg is NOW also a constant
          ++constants;
          constantSum += v;
        } else if (varIndex1 === -1) {
          TRACE('      - first non-constant');
          varIndex1 = index;
        } else if (varIndex2 === -1) {
          TRACE('      - second non-constant');
          varIndex2 = index;
        }
      }
    }

    TRACE(' -> There are now', constants, 'constants and', argCount - constants, 'actual vars. Constants sum to', constantSum, ', R=', domain__debug(R));
    TRACE(' -> Current args: ', Array.from(Array(argCount)).map((n, i) => domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)))).join(' '), ' Result:', domain__debug(R));

    let valuesToSumLeft = (argCount - constants) + (constantSum === 0 ? 0 : 1);

    TRACE(' - args:', argCount, ', constants:', constants, ', valuesToSumLeft=', valuesToSumLeft, ', constantSum=', constantSum, ', varIndex1=', varIndex1, ', varIndex2=', varIndex2);
    ASSERT(valuesToSumLeft > 0 || (constantSum === 0 && argCount === constants), 'a sum with args cant have no values left here unless there are only zeroes (it implies empty domains and should incur early returns)', valuesToSumLeft);

    if (valuesToSumLeft === 1) { // ignore constants if they are zero!
      TRACE(' - valuesToSumLeft = 1');
      ASSERT(varIndex2 === -1, 'we shouldnt have found a second var', varIndex2);
      ASSERT(constantSum > 0 ? varIndex1 === -1 : varIndex1 >= 0, 'with one value left it should either be a nonzero constant or an actual variable');
      if (constantSum > 0) {
        TRACE(' - Setting R to the sum of constants:', constantSum);
        let nR = domain_intersectionValue(R, constantSum);
        if (nR !== R) updateDomain(indexR, nR, 'min_sum');
      } else {
        TRACE(' - Aliasing R to the single var', varIndex1);
        intersectAndAlias(indexR, varIndex1, R, getDomain(varIndex1, true));
      }
      TRACE(' - eliminating constraint now');
      ml_eliminate(ml, offset, opSize);
    } else if (constants > 1 || (constants === 1 && constantSum === 0)) {
      TRACE(' - valuesToSumLeft > 1. Unable to morph but there are', constants, 'constants to collapse to a single arg with value', constantSum);
      // there are constants and they did not morph or eliminate the constraint; consolidate them.
      // loop backwards, remove all constants except one, move all other args back to compensate,
      // only update the index of the last constant, update the count, compile a jump for the new trailing space

      let newOpSize = opSize - (constants - (constantSum > 0 ? 1 : 0)) * 2;

      for (let i = argCount - 1; i >= 0 && constants; --i) {
        let argOffset = offsetArgs + i * 2;
        let index = readIndex(ml, argOffset);
        let domain = getDomainFast(index);
        TRACE('    - i=', i, ', index=', index, 'dom=', domain__debug(domain));
        if (domain_isSolved(domain)) {
          if (constants === 1 && constantSum !== 0) {
            // if constantSum>0 then we should encounter at least one constant to do this step on
            TRACE('      - Overwriting the last constant at', argOffset, 'with an index for total constant value', constantSum);
            let newConstantIndex = addVar(undefined, constantSum, false, false, true);
            ml_enc16(ml, offsetArgs + i * 2, newConstantIndex);
            break; // probably not that useful, might even be bad to break here
          } else {
            TRACE('      - found a constant to remove at', argOffset, ', moving further domains one space forward (from ', i + 1, ' / ', argCount, ')', i + 1 < argCount);
            ASSERT(constants > 0, 'should have some constants');
            min_spliceArgSlow(ml, offsetArgs, argCount, i, true); // also moves R
            --argCount;
          }
          --constants;
        }
      }

      ml_enc16(ml, offset + 1, argCount);
      // now "blank out" the space of eliminated constants, they should be at the end of the op
      ml_compileJumpSafe(ml, offset + newOpSize, opSize - newOpSize);

      TRACE(' - Cleaned up constant args');
      TRACE(' - ml for this sum now:', ml.slice(offset, offset + opSize).join(' '));
    } else {
      TRACE(' - unable to improve this sum at this time');
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + opSize;
    }
  }

  function min_spliceArgSlow(ml, argsOffset, argCount, argIndex, includingResult) {
    TRACE('      - min_spliceArgSlow(', argsOffset, argCount, argIndex, includingResult, ')');
    let toCopy = argCount;
    if (includingResult) ++toCopy;
    for (let i = argIndex + 1; i < toCopy; ++i) {
      let fromOffset = argsOffset + i * 2;
      let toOffset = argsOffset + (i - 1) * 2;
      TRACE('        - moving', ((includingResult && i === argCount - 1) ? 'R' : 'arg ' + (i + (includingResult ? 0 : 1)) + '/' + argCount), 'at', fromOffset, 'and', fromOffset + 1, 'moving to', toOffset, 'and', toOffset + 1);
      ml[toOffset] = ml[fromOffset];
      ml[toOffset + 1] = ml[fromOffset + 1];
    }
  }

  function min_product(ml, offset) {
    let offsetCount = offset + 1;
    let argCount = ml_dec16(ml, offsetCount);

    TRACE(' = min_product', argCount, 'x');

    if (argCount === 2) { // TODO: merge this
      if (min_product_2(ml, offset)) return;
    }

    let opSize = SIZEOF_C + argCount * 2 + 2;
    let offsetArgs = offset + SIZEOF_C;
    let offsetR = offset + opSize - 2;

    let indexR = readIndex(ml, offsetR);
    let R = getDomainFast(indexR);

    TRACE('  - ml for this product:', ml.slice(offset, offset + opSize).join(' '));
    TRACE('  - indexes:', indexR, '= product(', Array.from(Array(argCount)).map((n, i) => readIndex(ml, offsetArgs + i * 2)).join(', '), ')');
    TRACE('  - domains:', domain__debug(R), '= product(', Array.from(Array(argCount)).map((n, i) => domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)))).join(', '), ')');

    if (!R) return;

    // a product is basically a pyramid of muls; (A*B)*(C*D) etc
    // we loop back to front because we're splicing out vars while looping

    // replace all constants by one constant
    // prune the result var by intersecting it with the product of the actual args
    // in limited cases we can prune some of the arg values if the result forces
    // that (if the result is max 10 then inputs can be pruned of any value > 10)
    // we cant really do anything else

    TRACE(' - first loop to get the product of the args and constants');
    let product = domain_createValue(1);
    let constants = 0;
    let constantProduct = 1;
    for (let i = 0; i < argCount; ++i) {
      let index = readIndex(ml, offsetArgs + i * 2);
      let domain = getDomainFast(index);
      TRACE('    - i=', i, ', index=', index, 'dom=', domain__debug(domain), ', constant product before:', constantProduct);
      let v = domain_getValue(domain);
      if (v >= 0) {
        ++constants;
        constantProduct *= v;
      }
      product = domain_mul(product, domain);
    }

    TRACE(' - total product=', domain__debug(product), ', constantProduct=', constantProduct, 'with', constants, 'constants. applying to R', domain__debug(R), '=', domain__debug(domain_intersection(product, R)));

    let oR = R;

    if (constants === argCount) { // bit of an edge case, though it can happen after multiple passes
      TRACE(' - all product args are constants so R must simply eq their product, eliminating constraint;', domain__debug(R), '&', domain__debug(domain_createValue(constantProduct)), '=', domain__debug(domain_intersectionValue(R, constantProduct)));
      R = domain_intersectionValue(R, constantProduct);
      if (R !== oR) updateDomain(indexR, R, 'setting R to product of constants');
      ml_eliminate(ml, offset, opSize);
      return;
    }

    if (constantProduct === 0) {
      // edge case; if a constant produced zero then R will be zero and all args are free
      TRACE(' - there was a zero constant so R=0 and all args are free, eliminating constraint');
      R = domain_intersectionValue(R, 0);
      if (R !== oR) updateDomain(indexR, R, 'setting R to zero');
      ml_eliminate(ml, offset, opSize);
      return;
    }

    R = domain_intersection(product, R);
    TRACE(' - Updated R from', domain__debug(oR), 'to', domain__debug(R));
    if (R !== oR && updateDomain(indexR, R, 'product; updating R with outer bounds of its args;')) return;

    if (domain_isZero(R)) {
      TRACE(' - R=0 so at least one arg must be 0, morph this to a nall');
      ml_enc8(ml, offset, ML_NALL);
      ml_compileJumpSafe(ml, offset + opSize - 2, 2); // cuts off R
      return;
    }

    // from this point R isnt zero and none of the args is solved to zero (but could still have it in their domain!)
    // this simplifies certain decisions :)

    ASSERT(domain_invMul(R, constantProduct), 'R should be a multiple of the constant sum');
    ASSERT(domain_min(R) === 0 || Number.isFinite(domain_min(R) / constantProduct), 'min(R) should be the result of the constants multiplied by other values, so dividing it should result in an integer');
    ASSERT(Number.isFinite(domain_max(R) / constantProduct), 'max(R) should be the result of the constants multiplied by other values, so dividing it should result in an integer');

    // get R without constants to apply to var args
    let subR = constantProduct === 1 ? R : domain_invMul(R, domain_createValue(constantProduct));
    ASSERT(subR, 'R-constants should not be empty');

    TRACE(' - Now back propagating R to the args, R without constants:', domain__debug(subR));

    // we can only trim bounds, not a full intersection (!)
    // note that trimming may lead to more constants so dont eliminate them here (KIS)
    let minSR = domain_min(subR);
    let maxSR = domain_max(subR);
    let atLeastOneArgHadZero = false; // any zero can blow up the result to 0, regardless of other args
    let varIndex1 = -1; // track non-constants for quick optimizations for one or two vars
    let varIndex2 = -1;
    for (let i = 0; i < argCount; ++i) {
      let index = readIndex(ml, offsetArgs + i * 2);
      let domain = getDomainFast(index);
      TRACE('    - i=', i, ', index=', index, 'dom=', domain__debug(domain));
      let v = domain_getValue(domain);
      if (v === 0) atLeastOneArgHadZero = true; // probably not very useful
      if (v < 0) { // ignore constants
        if (!atLeastOneArgHadZero && domain_hasZero(domain)) atLeastOneArgHadZero = true;
        // so the idea is that any value in an arg that could not even appear in R if all other args
        // were zero, is a value that cant ever yield a solution. those are the values we trim here.
        // this process takes constants in account (hence subR) because they don't have a choice.
        let newDomain = domain_removeLtUnsafe(domain, minSR);
        newDomain = domain_removeGtUnsafe(domain, maxSR);
        if (newDomain !== domain && updateDomain(index, newDomain, 'product arg; trim invalid values')) return;

        v = domain_getValue(newDomain);
        if (v >= 0) {
          TRACE('      - constant', v);
          // arg is NOW also a constant
          ++constants;
          constantProduct += v;
        } else if (varIndex1 === -1) {
          TRACE('      - first non-constant');
          varIndex1 = index;
        } else if (varIndex2 === -1) {
          TRACE('      - second non-constant');
          varIndex2 = index;
        }
      }
    }

    TRACE(' -> There are now', constants, 'constants and', argCount - constants, 'actual vars. Constants mul to', constantProduct, ', R=', domain__debug(R));
    TRACE(' -> Current args: ', Array.from(Array(argCount)).map((n, i) => domain__debug(getDomainFast(readIndex(ml, offsetArgs + i * 2)))).join(' '), ' Result:', domain__debug(R));

    let valuesToMulLeft = (argCount - constants) + (constantProduct === 1 ? 0 : 1);
    ASSERT(valuesToMulLeft > 0 || (constantProduct === 1 && argCount === constants), 'a product with args cant have no values left here unless the constants are all 1 (it implies empty domains and should incur early returns)', valuesToMulLeft);

    if (valuesToMulLeft === 1) { // ignore constants if they are zero!
      ASSERT(varIndex2 === -1, 'we shouldnt have found a second var', varIndex2);

      if (constantProduct !== 1) {
        TRACE(' - Setting R to the product of constants:', constantProduct, '(and a zero?', atLeastOneArgHadZero, ')');
        if (atLeastOneArgHadZero) {
          TRACE('   - Updating to a booly-pair:', domain__debug(domain_createBoolyPair(constantProduct)));
          let nR = domain_intersection(R, domain_createBoolyPair(constantProduct));
          if (nR !== R) updateDomain(indexR, nR, 'min_product');
        } else {
          TRACE('   - Updating to a solved value:', constantProduct);
          let nR = domain_intersectionValue(R, constantProduct);
          if (nR !== R) updateDomain(indexR, nR, 'min_product');
        }
      } else {
        TRACE(' - Aliasing R to the single var', varIndex1);
        intersectAndAlias(indexR, varIndex1, R, getDomain(varIndex1, true));
      }
      TRACE(' - eliminating constraint now');
      ml_eliminate(ml, offset, opSize);
    } else if (constants > 1) {
      TRACE(' - Unable to morph but there are', constants, 'constants to collapse to a single arg with value', constantProduct);
      // there are constants and they did not morph or eliminate the constraint; consolidate them.
      // loop backwards, remove all constants except one, move all other args back to compensate,
      // only update the index of the last constant, update the count, compile a jump for the new trailing space

      let newOpSize = opSize - (constants - 1) * 2;

      for (let i = argCount - 1; i >= 0 && constants; --i) {
        let index = readIndex(ml, offsetArgs + i * 2);
        let domain = getDomainFast(index);
        TRACE('    - i=', i, ', index=', index, 'dom=', domain__debug(domain), ', constant?', domain_isSolved(domain));
        if (domain_isSolved(domain)) {
          if (constants === 1) {
            TRACE(' - Overwriting the last constant with an index for the total constant value');
            let index = addVar(undefined, constantProduct, false, false, true);
            ml_enc16(ml, offsetArgs + i * 2, index);
          } else {
            TRACE('  - found a constant, moving further domains one space forward (from ', i + 1, ' / ', argCount, ')', i + 1 < argCount);
            ASSERT(constants > 0, 'should have some constants');
            min_spliceArgSlow(ml, offsetArgs, argCount, i, true); // move R as well
            --argCount;
          }
          --constants;
        }
      }

      let emptySpace = opSize - newOpSize;
      TRACE(' - constants squashed, compiling new length (', argCount, ') and a jump for the empty space (', emptySpace, 'bytes )');
      ml_enc16(ml, offset + 1, argCount);
      // now "blank out" the space of eliminated constants, they should be at the end of the op
      ASSERT(emptySpace > 0, 'since at least two constants were squashed there should be some bytes empty now');
      ml_compileJumpSafe(ml, offset + newOpSize, emptySpace);

      TRACE(' - ml for this product now:', ml.slice(offset, offset + opSize).join(' '));
      ASSERT(ml_validateSkeleton(ml, 'min_product; case 3'));

      TRACE(' - Cleaned up constant args');
    } else {
      TRACE(' - not only jumps...');
      onlyJumps = false;
      pc = offset + opSize;
    }
  }

  function min_all(ml, offset) {
    // loop through the args and remove zero from all of them. then eliminate the constraint. it is an artifact.
    let argCount = ml_dec16(ml, offset + 1);

    TRACE(' = min_all', argCount, 'x. removing zero from all args and eliminating constraint');

    for (let i = 0; i < argCount; ++i) {
      let indexD = readIndex(ml, offset + SIZEOF_C + i * 2);
      let oD = getDomain(indexD, true);
      let D = domain_removeValue(oD, 0);
      if (oD !== D) updateDomain(indexD, D, 'ALL D');
    }

    ml_eliminate(ml, offset, SIZEOF_C + argCount * 2);
  }

  function min_some_2(ml, offset) {
    let offsetA = offset + OFFSET_C_A;
    let offsetB = offset + OFFSET_C_B;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);

    TRACE(' = min_some_2', indexA, '|', indexB, '   ->   ', domain__debug(A), '|', domain__debug(B));
    if (!A || !B) return true;

    if (indexA === indexB) {
      TRACE(' - argcount=2 and indexA==indexB. so A>0 and eliminating constraint');
      let nA = domain_removeValue(A, 0);
      if (A !== nA) updateDomain(indexA, nA, 'A|A');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_isZero(A)) {
      TRACE(' - A=0 so remove 0 from B', domain__debug(B), '->', domain__debug(domain_removeValue(B, 0)));
      let oB = B;
      B = domain_removeValue(oB, 0);
      if (B !== oB) updateDomain(indexB, B, 'OR B');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    if (domain_isZero(B)) {
      TRACE(' - B=0 so remove 0 from A', domain__debug(A), '->', domain__debug(domain_removeValue(A, 0)));
      let oA = A;
      A = domain_removeValue(oA, 0);
      if (A !== oA) updateDomain(indexA, A, 'OR A');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    if (domain_hasNoZero(A) || domain_hasNoZero(B)) {
      TRACE(' - at least A or B has no zero so remove constraint');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return true;
    }

    TRACE(' - min_some_2 changed nothing');
    return false;
  }

  function min_none(ml, offset) {
    let argCount = ml_dec16(ml, offset + 1);
    TRACE(' = min_none on', argCount, 'vars. Setting them all to zero and removing constraint.'); // This is an artifact and that is fine.

    for (let i = 0; i < argCount; ++i) {
      let indexD = readIndex(ml, offset + SIZEOF_C + i * 2);
      let D = getDomain(indexD, true);
      let nD = domain_removeGtUnsafe(D, 0);
      if (D !== nD) updateDomain(indexD, nD);
    }

    ml_eliminate(ml, offset, SIZEOF_C + argCount * 2);
  }

  function min_xor(ml, offset) {
    let offsetA = offset + OFFSET_C_A;
    let offsetB = offset + OFFSET_C_B;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);

    TRACE(' = min_xor', indexA, '^', indexB, '   ->   ', domain__debug(A), '^', domain__debug(B));
    if (!A || !B) return;

    if (indexA === indexB) {
      TRACE(' - index A === index B, x^x is falsum');
      setEmpty(indexA, 'x^x');
      emptyDomain = true;
      return;
    }

    if (domain_isZero(A)) {
      TRACE(' - A=0 so B must be >=1');
      let oB = B;
      B = domain_removeValue(B, 0);
      if (B !== oB) updateDomain(indexB, B, 'xor B>=1');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_isZero(B)) {
      TRACE(' - B=0 so A must be >=1');
      let oA = A;
      A = domain_removeValue(A, 0);
      if (A !== oA) updateDomain(indexA, A, 'xor A>=1');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_hasNoZero(A)) {
      TRACE(' - A>=1 so B must be 0');
      let oB = B;
      B = domain_removeGtUnsafe(B, 0);
      if (B !== oB) updateDomain(indexB, B, 'xor B=0');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_hasNoZero(B)) {
      TRACE(' - B>=1 so A must be 0');
      let oA = A;
      A = domain_removeGtUnsafe(A, 0);
      if (A !== oA) updateDomain(indexA, A, 'xor A=0');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    TRACE(' - not only jumps...');
    onlyJumps = false;
    pc = offset + SIZEOF_C_2;
  }

  function min_xnor(ml, offset) {
    let argCount = ml_dec16(ml, offset + 1);

    TRACE(' = min_xnor;', argCount, 'args');

    if (argCount !== 2) {
      TRACE(' - xnor does not have 2 args, bailing for now');
      onlyJumps = false;
      pc = offset + SIZEOF_C + argCount * 2;
      return;
    }

    let offsetA = offset + OFFSET_C_A;
    let offsetB = offset + OFFSET_C_B;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);

    TRACE(' -', indexA, '!^', indexB, '   ->   ', domain__debug(A), '!^', domain__debug(B));
    if (!A || !B) return;
    ASSERT(ml_dec16(ml, offset + 1) === 2, 'should have 2 args now');

    if (indexA === indexB) {
      TRACE('   - oh... it was the same index. removing op'); // artifact, can happen
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_isZero(A)) {
      TRACE(' - A=0 so B must be 0');
      let oB = B;
      B = domain_removeGtUnsafe(B, 0);
      if (B !== oB) updateDomain(indexB, B, 'xnor B');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_isZero(B)) {
      TRACE(' - B=0 so A must be 0');
      let oA = A;
      A = domain_removeGtUnsafe(A, 0);
      if (A !== oA) updateDomain(indexA, A, 'xnor A');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_hasNoZero(A)) {
      TRACE(' - A>=1 so B must be >=1');
      let oB = B;
      B = domain_removeValue(B, 0);
      if (B !== oB) updateDomain(indexB, B, 'xnor B');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_hasNoZero(B)) {
      TRACE(' - B>=1 so A must be >=1');
      let oA = A;
      A = domain_removeValue(A, 0);
      if (A !== oA) updateDomain(indexA, A, 'xnor A');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    // A and B are booly-pairs and equal then they can be considered an alias
    if (A === B && domain_size(A) === 2) {
      TRACE(' - A==B, size(A)=2 so size(B)=2 so max(A)==max(B) so under XNOR: A==B;', domain__debug(A), '!^', domain__debug(B));
      ASSERT(domain_size(B) === 2, 'If A==B and size(A)=2 then size(B) must also be 2 and they are regular aliases');
      addAlias(indexA, indexB);
      varChanged = true;
      return;
      // note: cutter supports more cases for xnor pseudo alias, but that requires knowing BOOLY state for each var
    }

    TRACE(' - not only jumps...');
    onlyJumps = false;
    pc = offset + SIZEOF_C_2;
  }

  function min_imp(ml, offset) {
    let offsetA = offset + OFFSET_C_A;
    let offsetB = offset + OFFSET_C_B;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);

    TRACE(' = min_imp', indexA, '->', indexB, '   ->   ', domain__debug(A), '->', domain__debug(B));
    if (!A || !B) return;

    if (indexA === indexB) {
      TRACE(' - same index, tautology, eliminating constraint');
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    // if A is nonzero then B must be nonzero and constraint is solved
    // if A is zero then constraint is solved
    // if B is nonzero then constraint is solved
    // if B is zero then A must be zero

    if (domain_isZero(A)) {
      TRACE(' - A is zero so just eliminate the constraint');
      // eliminate constraint. B is irrelevant now.
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_hasNoZero(A)) {
      TRACE(' - A is nonzero so remove zero from B and eliminate the constraint');
      // remove zero from B, eliminate constraint
      let oB = B;
      B = domain_removeValue(oB, 0);
      if (oB !== B) updateDomain(indexB, B, 'IMP B');

      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_isZero(B)) {
      TRACE(' - B is zero so set A to zero and eliminate the constraint');
      // remove zero from A, eliminate constraint
      let oA = A;
      A = domain_removeGtUnsafe(oA, 0);
      if (oA !== A) updateDomain(indexA, A, 'IMP A');

      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    if (domain_hasNoZero(B)) {
      TRACE(' - B is nonzero so just eliminate the constraint');
      // eliminate constraint. A is irrelevant now.
      ml_eliminate(ml, offset, SIZEOF_C_2);
      return;
    }

    TRACE(' - not only jumps...');
    onlyJumps = false;
    pc = offset + SIZEOF_C_2;
  }

  function min_nimp(ml, offset) {
    let offsetA = offset + OFFSET_C_A;
    let offsetB = offset + OFFSET_C_B;
    let indexA = readIndex(ml, offsetA);
    let indexB = readIndex(ml, offsetB);
    let A = getDomainFast(indexA);
    let B = getDomainFast(indexB);

    TRACE(' = min_nimp', indexA, '!->', indexB, '   ->   ', domain__debug(A), '!->', domain__debug(B));
    if (!A || !B) return;

    // nimp is trivial since A must be nonzero and B must be zero

    let oA = A;
    A = domain_removeValue(oA, 0);
    if (oA !== A) updateDomain(indexA, A, 'NIMP A');

    let oB = B;
    B = domain_removeGtUnsafe(oB, 0);
    if (oB !== B) updateDomain(indexB, B, 'NIMP B');

    TRACE(' ->', domain__debug(A), '!->', domain__debug(B));

    ml_eliminate(ml, offset, SIZEOF_C_2);
  }
}

// BODY_STOP

export {
  min_run,
  min_optimizeConstraints,
};
