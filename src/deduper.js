import {
  ASSERT,
  getTerm,
  TRACE,
} from '../../fdlib/src/helpers';
import {
  domain__debug,
  domain_containsValue,
  domain_createValue,
  domain_getValue,
  domain_isBooly,
  domain_isBoolyPair,
  domain_isZero,
  domain_size,
  domain_hasNoZero,
  domain_intersection,
  domain_isSolved,
  domain_removeGtUnsafe,
  domain_removeValue,
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

  OFFSET_C_A,
  OFFSET_C_B,
  OFFSET_C_R,

  SIZEOF_V,
  SIZEOF_W,
  SIZEOF_VVV,
  SIZEOF_C,
  SIZEOF_C_2,
  SIZEOF_CR_2,

  ml__debug,
  ml_cr2c2,
  ml_dec16,
  ml_dec32,
  ml_eliminate,
  ml_getOpSizeSlow,
  ml_heapSort16bitInline,
  ml_throw,
  ml_vvv2c2,
} from './ml';
import {
  m2d__debug,
} from './ml2dsl';

// BODY_START

// these global counters can be used to trace problems or print a dsl at explicit steps in the solve
let __runCounter = 0;
let __opCounter = 0;

function deduper(ml, problem) {
  ++__runCounter;
  TRACE('\n ## pr_dedupe, counter=', __runCounter, ',ml=', ml.length < 50 ? ml.join(' ') : '<big>');

  let getDomain = problem.getDomain;
  let setDomain = problem.setDomain;
  let getAlias = problem.getAlias;
  let addVar = problem.addVar;
  let addAlias = problem.addAlias;

  let pc = 0;
  let constraintHash = {}; // keys are A@B or R=A@B and the vars can be an index (as is) or a literal prefixed with #
  let debugHash = {};
  let removed = 0;
  let aliased = 0;
  let emptyDomain = false;
  innerLoop();
  getTerm().log(' - dedupe removed', removed, 'constraints and aliased', aliased, 'result vars, emptyDomain=', emptyDomain, ', processed', __opCounter, 'ops');
  TRACE(m2d__debug(problem));

  return emptyDomain ? -1 : aliased; // if aliases were created the minifier will want another go.

  function dedupePairOc2(op) {
    let indexA = getAlias(ml_dec16(ml, pc + OFFSET_C_A));
    let indexB = getAlias(ml_dec16(ml, pc + OFFSET_C_B));

    let key = op + ':' + indexA + ',' + indexB;
    let debugString = op + ':' + domain__debug(getDomain(indexA, true)) + ',' + domain__debug(getDomain(indexB, true));

    if (op === '<' || op === '<=') {
      if (checkLtLteFromRegular(op, indexA, indexB, debugString)) return;
    }

    // below this line no more deduping, only appending

    if (constraintHash[key] !== undefined) {
      TRACE(' - dedupePairOc2; Found dupe constraint; eliminating the second one');
      TRACE('    - #1:', debugHash[key]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, SIZEOF_C_2);
      return;
    }

    constraintHash[key] = 1;
    debugHash[key] = debugString;
    pc += SIZEOF_C_2;
  }

  function checkLtLteFromRegular(op, indexA, indexB, debugString) {
    // check whether reifiers have matching non-reifiers (valid artifacts), so `R=A<?B` and `A<B` means `R>0`
    // R>0 when: '<? <' '<=? <' '<=? <='
    // R=? when: '<? <=' (because the A==B case always passes '<=' while '<?' depends on R)
    TRACE('   - checking for matching regular inverted constraints');
    ASSERT(op === '<' || op === '<=', 'update this code if this assertion changes', op);

    // search for
    // - R=A<?B A<B
    // - R=A<=?B A<B
    // - R=A<=?B A<=B
    // => R>0
    if (op === '<' && checkLtLteFromRegularAB('<?', '<', indexA, indexB, debugString)) return true;
    if (op === '<' && checkLtLteFromRegularAB('<=?', '<', indexA, indexB, debugString)) return true;
    if (op === '<=' && checkLtLteFromRegularAB('<=?', '<=', indexA, indexB, debugString)) return true;

    // search for
    // - R=A<?B B<A
    // - R=A<?B B<=A
    // - R=A<=?B B<A
    // => R=0
    if (op === '<' && checkLtLteFromRegularBA('<?', '<', indexA, indexB, debugString)) return true;
    if (op === '<=' && checkLtLteFromRegularBA('<?', '<=', indexA, indexB, debugString)) return true;
    if (op === '<' && checkLtLteFromRegularBA('<=?', '<', indexA, indexB, debugString)) return true;

    return false;
  }
  function checkLtLteFromRegularAB(rifop, regop, indexA, indexB, debugString) {
    let rifKey = rifop + ':R=' + indexA + ',' + indexB;
    let reifierOffset = constraintHash[rifKey];
    if (reifierOffset) {
      let indexR = getAlias(ml_dec16(ml, reifierOffset + 5));
      let R = getDomain(indexR, true);
      if (!domain_isBooly(R)) return false;
      TRACE(' - checkLtLteFromReifierAB; found `R=A' + rifop + 'B` and `A' + regop + 'B`, eliminating reifier and booly-solving R, R=', domain__debug(R));
      TRACE('    - #1:', debugHash[rifKey]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, reifierOffset, SIZEOF_VVV);
      TRACE(' - Removing 0 from R');
      setDomain(indexR, domain_removeValue(R, 0));
      return true;
    }
    return false;
  }
  function checkLtLteFromRegularBA(rifop, regop, indexA, indexB, debugString) {
    let invRifKey = rifop + ':R=' + indexB + ',' + indexA;
    let reifierOffset = constraintHash[invRifKey];
    if (reifierOffset) {
      let indexR = getAlias(ml_dec16(ml, reifierOffset + 5));
      let R = getDomain(indexR, true);
      if (!domain_isBooly(R)) return false;
      TRACE(' - checkLtLteFromReifierBA; found `R=A' + rifop + 'B` and `B' + regop + 'A`, eliminating reifier and booly-solving R, R=', domain__debug(R));
      TRACE('    - #1:', debugHash[invRifKey]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, reifierOffset, SIZEOF_VVV);
      TRACE(' - Setting R to 0');
      setDomain(indexR, domain_removeGtUnsafe(R, 0));
      return true;
    }
    return false;
  }

  function dedupeTripO(op) {
    // this assumes the assignment is a fixed value, not booly like reifiers
    // because in this case we can safely alias any R that with the same A@B

    let indexA = getAlias(ml_dec16(ml, pc + 1));
    let indexB = getAlias(ml_dec16(ml, pc + 3));
    let indexR = getAlias(ml_dec16(ml, pc + 5));

    let key = op + ':' + indexA + ',' + indexB;
    let debugString = op + ':' + domain__debug(getDomain(indexR, true)) + '=' + domain__debug(getDomain(indexA, true)) + ',' + domain__debug(getDomain(indexB, true));

    let index = constraintHash[key];
    if (index !== undefined) {
      index = getAlias(index);
      TRACE(' - dedupeTripO; Found dupe constraint; eliminating the second one, aliasing', indexR, 'to', index);
      TRACE('    - #1:', debugHash[key]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, SIZEOF_VVV);
      if (indexR !== index) {
        let R = domain_intersection(getDomain(indexR, true), getDomain(index, true));
        if (!R) return emptyDomain = true;
        // this probably wont matter for most of the cases, but it could make a difference
        //setDomain(indexR, R); // (useless)
        setDomain(index, R);
        addAlias(indexR, index);
      }
      return;
    }

    constraintHash[key] = indexR;
    debugHash[key] = debugString;
    pc += SIZEOF_VVV;
  }

  function dedupeIsltIslte(op) {
    // islt, islte

    let offset = pc;

    let indexA = getAlias(ml_dec16(ml, pc + 1));
    let indexB = getAlias(ml_dec16(ml, pc + 3));
    let indexR = getAlias(ml_dec16(ml, pc + 5));

    // we'll add a key by all three indexes and conditionally also on the args and the domain of R

    let key = op + ':' + indexR + '=' + indexA + ',' + indexB;
    let debugString = op + ':' + domain__debug(getDomain(indexR, true)) + '=' + domain__debug(getDomain(indexA, true)) + ',' + domain__debug(getDomain(indexB, true));

    TRACE('   - key=', key, ';', constraintHash[key] !== undefined);
    if (constraintHash[key] !== undefined) {
      TRACE(' - dedupeReifierTripU; Found dupe constraint; eliminating the second one');
      TRACE('    - #1:', debugHash[key]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, SIZEOF_VVV);
      return;
    }

    let R = getDomain(indexR, true);

    TRACE('   - checking for matching regular constraints');
    ASSERT(op.slice(0, -1) === '<' || op.slice(0, -1) === '<=', 'update this code if this assertion changes');
    let regkey = op.slice(0, -1) + ':' + indexA + ',' + indexB;
    if (constraintHash[regkey]) {
      TRACE(' - dedupeReifierTripU; found R=A' + op + 'B and A' + op.slice(0, -1) + 'B, eliminating reifier and forcing R to truthy if R has a nonzero, R=', domain__debug(R));
      if (!domain_isZero(R)) { // has non-zero
        TRACE('    - #1:', debugHash[regkey]);
        TRACE('    - #2:', debugString);
        ml_eliminate(ml, pc, SIZEOF_VVV);
        TRACE(' - Removing 0 from R');
        setDomain(indexR, domain_removeValue(R, 0));
        return;
      }
    }

    if (checkLtLteFromReifier(op, indexA, indexB, indexR, R, debugString)) return;

    let invkey = (op === '<?' ? '<=?' : '<?') + ':R=' + indexB + ',' + indexA;
    let invOffset = constraintHash[invkey];
    if (invOffset) {
      // one of:
      // R = A <? B, S = B <=? A
      // R = A <=? B, S = B <? A
      // (note: not <?<? nor <=?<=? because they are NOT their own inverse)

      TRACE(' - Found `', (op === '<?' ? 'R = A <? B, S = B <=? A' : 'R = A <=? B, S = B <? A'), '`');
      let indexS = getAlias(ml_dec16(ml, invOffset + 5));
      TRACE(' - morphing one op to `R ^ S`;', domain__debug(getDomain(indexR)), '^', domain__debug(getDomain(indexS)));
      ml_vvv2c2(ml, offset, ML_XOR, indexR, indexS);
      return;
    }

    TRACE('   - R:', domain__debug(R), ', size=', domain_size(R), ', has zero:', !domain_hasNoZero(R), '--> is safe?', domain_isBoolyPair(R));
    if (domain_isBoolyPair(R)) {
      // okay R has only two values and one of them is zero
      // try to match the arg constraints only. if we find a dupe with
      // the same R domain then we can alias that R with this one
      // otherwise the two R's are pseudo xnor aliases

      // we'll encode the domain instead of indexR to prevent
      // multiple args on different R's to clash

      // while R may not look it, it still represents a unique domain so we can use the
      // encoded value as is here. wrap it to prevent clashes with indexes and numdoms
      let key2 = op + ':[' + R + ']' + '=' + indexA + ',' + indexB;
      TRACE('   - key2:', key2);

      let index = constraintHash[key2];
      if (index !== undefined) {
        index = getAlias(index);
        TRACE(' - dedupeIsltIslte; Found dupe reifier; eliminating the second one, aliasing', indexR, 'to', index);
        TRACE('    - #1:', debugHash[key2]);
        TRACE('    - #2:', debugString);
        ml_eliminate(ml, pc, SIZEOF_VVV);
        if (indexR === index) {
          TRACE(' - same indexes (perhaps aliased) so dont alias them here');
        } else {
          addAlias(indexR, index);
        }
        return;
      }

      constraintHash[key2] = indexR;
      debugHash[key2] = debugString;
    }

    constraintHash[key] = 1;
    debugHash[key] = debugString;

    let keyr = op + ':R=' + indexA + ',' + indexB;
    constraintHash[keyr] = offset;
    debugHash[keyr] = debugString;

    pc += SIZEOF_VVV;
  }

  function checkLtLteFromReifier(op, indexA, indexB, indexR, R, debugString) {
    // check whether reifiers have matching non-reifiers (valid artifacts), so `R=A<?B` and `A<B` means `R>0`
    // R>0 when: '<? <' '<=? <' '<=? <='
    // R=? when: '<? <=' (because the A==B case always passes '<=' while '<?' depends on R)
    TRACE('   - checking for matching regular inverted constraints');
    let regop = op.slice(0, -1);
    ASSERT(regop === '<' || regop === '<=', 'update this code if this assertion changes');
    if (domain_isBooly(R)) {
      // search for
      // - R=A<?B A<B
      // - R=A<=?B A<B
      // - R=A<=?B A<=B
      // => R>0
      if (op === '<?' && checkLtLteFromReifierAB('<?', '<', indexA, indexB, indexR, R, debugString)) return true;
      if (op === '<=?' && checkLtLteFromReifierAB('<=?', '<', indexA, indexB, indexR, R, debugString)) return true;
      if (op === '<=?' && checkLtLteFromReifierAB('<=?', '<=', indexA, indexB, indexR, R, debugString)) return true;

      // search for
      // - R=A<?B B<A
      // - R=A<?B B<=A
      // - R=A<=?B B<A
      // => R=0
      if (op === '<?' && checkLtLteFromReifierBA('<?', '<', indexA, indexB, indexR, R, debugString)) return true;
      if (op === '<?' && checkLtLteFromReifierBA('<?', '<=', indexA, indexB, indexR, R, debugString)) return true;
      if (op === '<=?' && checkLtLteFromReifierBA('<=?', '<', indexA, indexB, indexR, R, debugString)) return true;
    }
    return false;
  }
  function checkLtLteFromReifierAB(rifop, regop, indexA, indexB, indexR, R, debugString) {
    let regkey = regop + ':' + indexA + ',' + indexB;
    if (constraintHash[regkey]) {
      TRACE(' - checkLtLteFromReifierAB; found `R=A' + rifop + 'B` and `A' + regop + 'B`, eliminating reifier and booly-solving R, R=', domain__debug(R));
      TRACE('    - #1:', debugHash[regkey]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, SIZEOF_VVV);
      TRACE(' - Removing 0 from R');
      setDomain(indexR, domain_removeValue(R, 0));
      return true;
    }
    return false;
  }
  function checkLtLteFromReifierBA(rifop, regop, indexA, indexB, indexR, R, debugString) {
    let reginvkey = regop + ':' + indexB + ',' + indexA;
    if (constraintHash[reginvkey]) {
      TRACE(' - checkLtLteFromReifierBA; found `R=A' + rifop + 'B` and `B' + regop + 'A`, eliminating reifier and booly-solving R, R=', domain__debug(R));
      TRACE('    - #1:', debugHash[reginvkey]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, SIZEOF_VVV);
      TRACE(' - Setting R to 0');
      setDomain(indexR, domain_removeGtUnsafe(R, 0));
      return true;
    }
    return false;
  }

  function dedupeBoolyList(op) {
    // isall, isnall, isnone, issome
    // the tricky example:
    // ####
    // : A, B, C 1
    // : R [0 1]
    // : S [0 0 2 2]
    // R = xxx?(A B C)
    // S = xxx?(A B C)
    // ####
    // in this case R and S are "booly alias" but not actual alias
    // basically this translates into a xnor (if R then S, if S then R)

    let argCount = ml_dec16(ml, pc + 1);
    let opSize = SIZEOF_C + argCount * 2 + 2;

    TRACE(' - dedupeBoolyList; args:', argCount, ', opsize:', opSize);

    // first we want to sort the list. we'll do this inline to prevent array creation
    ml_heapSort16bitInline(ml, pc + SIZEOF_C, argCount);

    // now collect them. the key should end up with an ordered list
    let args = '';
    let debugArgs = '';
    for (let i = 0; i < argCount; ++i) {
      let index = getAlias(ml_dec16(ml, pc + SIZEOF_C + i * 2));
      args += index + ' ';
      debugArgs += domain__debug(getDomain(index, true));
    }

    let indexR = getAlias(ml_dec16(ml, pc + SIZEOF_C + argCount * 2));

    // we'll add a key with indexR and conditionally one with just the domain of R

    let key = op + ':' + indexR + '=' + args;
    let debugString = op + ':' + domain__debug(getDomain(indexR, true)) + '=' + debugArgs;

    TRACE('   - key=', key, ';', constraintHash[key] !== undefined);
    if (constraintHash[key] !== undefined) {
      TRACE(' - dedupeBoolyList; Found dupe constraint; eliminating the second one');
      TRACE('    - #1:', debugHash[key]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, opSize);
      return;
    }

    constraintHash[key] = 1;
    debugHash[key] = debugString;

    let R = getDomain(indexR, true);
    TRACE('   - R:', domain__debug(R), '--> is safe?', domain_isBoolyPair(R));
    if (domain_isBoolyPair(R)) {
      // okay R has only two values and one of them is zero
      // try to match the arg constraints only. if we find a dupe with
      // the same R domain then we can alias that R with this one

      // we'll encode the domain instead of indexR to prevent
      // multiple args on different R's to clash

      // while R may not look it, it still represents a unique domain so we can use the
      // encoded value as is here. wrap it to prevent clashes with indexes and numdoms
      let key2 = op + ':[' + R + ']' + '=' + args;
      TRACE('   - key2:', key2);

      let index = constraintHash[key2];
      if (index !== undefined) {
        index = getAlias(index);
        TRACE(' - dedupeBoolyList; Found dupe reifier; eliminating the second one, aliasing', indexR, 'to', index);
        TRACE('    - #1:', debugHash[key2]);
        TRACE('    - #2:', debugString);
        ml_eliminate(ml, pc, opSize);
        if (indexR === index) {
          TRACE(' - same indexes (perhaps aliased) so dont alias them here');
        } else {
          ASSERT(getDomain(indexR) === getDomain(index), 'should have already asserted that these two domains have only two values, a zero and a non-zero, and that they are equal');
          addAlias(indexR, index);
        }
        return;
      }

      constraintHash[key2] = indexR;
      debugHash[key2] = debugString;
    }

    TRACE(' - (no action, dedupeBoolyList)');
    pc += opSize;
  }

  function dedupeNonBoolyList(op) {
    // sum, product

    let argCount = ml_dec16(ml, pc + 1);
    let opSize = SIZEOF_C + argCount * 2 + 2;

    // first we want to sort the list. we'll do this inline to prevent array creation
    ml_heapSort16bitInline(ml, pc + SIZEOF_C, argCount);

    // now collect them. the key should end up with an ordered list
    let args = '';
    let debugArgs = '';
    for (let i = 0; i < argCount; ++i) {
      let argIndex = getAlias(ml_dec16(ml, pc + SIZEOF_C + i * 2));
      args += argIndex + ' ';
      debugArgs += domain__debug(getDomain(argIndex, true));
    }

    let indexR = getAlias(ml_dec16(ml, pc + SIZEOF_C + argCount * 2));

    // we'll add a key without indexR because the results of these ops are fixed (unlike booly ops)

    let key = op + ':' + '=' + args;
    let debugString = op + ':' + debugArgs;

    let index = constraintHash[key];
    if (index !== undefined) {
      index = getAlias(index);
      TRACE(' - dedupeNonBoolyList; Found dupe reifier; eliminating the second one, aliasing', indexR, 'to', index);
      TRACE('    - #1:', debugHash[key]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, opSize);
      if (indexR !== index) { // R = A <=? A (artifact)
        let domain = domain_intersection(getDomain(index, true), getDomain(indexR, true));
        setDomain(index, domain);
        addAlias(indexR, index);
      }
      return;
    }

    constraintHash[key] = indexR;
    debugHash[key] = debugString;

    pc += opSize;
  }

  function dedupeVoidList(op) {
    // sum, product

    let argCount = ml_dec16(ml, pc + 1);
    let opSize = SIZEOF_C + argCount * 2;

    // first we want to sort the list. we'll do this inline to prevent array creation
    ml_heapSort16bitInline(ml, pc + SIZEOF_C, argCount);

    // now collect them. the key should end up with an ordered list
    let args = '';
    let debugArgs = '';
    for (let i = 0; i < argCount; ++i) {
      let argIndex = getAlias(ml_dec16(ml, pc + SIZEOF_C + i * 2));
      args += argIndex + ' ';
      debugArgs += domain__debug(getDomain(argIndex, true));
    }

    let key = op + ':' + '=' + args;
    let debugString = op + ':' + debugArgs;

    if (constraintHash[key] !== undefined) {
      TRACE(' - dedupeVoidList; Found dupe constraint; eliminating the second one');
      TRACE('    - #1:', debugHash[key]);
      TRACE('    - #2:', debugString);
      ml_eliminate(ml, pc, opSize);
      return;
    }

    constraintHash[key] = 1;
    debugHash[key] = debugString;

    pc += opSize;
  }

  function dedupeInvIsSameIsDiff(op) {
    TRACE(' - dedupeInvIsSameIsDiff;', op);
    // looking for this pattern:
    // : X [2 3]
    // R = X ==? 2
    // S = X !=? 3
    // which means R !^ S, or even == when R and S are size=2,min=0,R==S

    let argCount = ml_dec16(ml, pc + 1);
    if (argCount !== 2) { // TODO: support any number of args here
      TRACE('   - arg count != 2 so bailing, for now');
      return false;
    }

    let indexA = getAlias(ml_dec16(ml, pc + OFFSET_C_A));
    let indexB = getAlias(ml_dec16(ml, pc + OFFSET_C_B));
    let indexR = getAlias(ml_dec16(ml, pc + OFFSET_C_R));

    // if A or B is a constant, then B will be a constant afterwards, and A (only) as well if they are both constants
    if (indexB < indexA) {
      let t = indexB;
      indexB = indexA;
      indexA = t;
    }

    let A = getDomain(indexA, true);
    let B = getDomain(indexB, true);

    // verify fingerprint
    if (domain_size(A) !== 2) {
      TRACE(' - size(A) != 2, bailing');
      return false;
    }

    let vB = domain_getValue(B);
    if (vB < 0 || !domain_containsValue(A, vB)) {
      TRACE(' - B wasnt a constant or A didnt contain B, bailing', domain__debug(A), domain__debug(B));
      return false;
    }

    // fingerprint matches. A contains the solved value B and one other value
    // check if opposite op is known

    let invA = domain_removeValue(A, vB);
    ASSERT(domain_isSolved(invA), 'if A had two values and one of them vB, then invA should have one value');
    let otherValue = domain_getValue(invA);
    let indexInvA = addVar(undefined, otherValue, false, false, true); // just gets the index for this constant
    ASSERT(getDomain(indexInvA) === domain_createValue(otherValue), 'should alias to a constant');
    let invOp = op === 'issame' ? 'isdiff' : 'issame';
    let key = invOp + ':' + indexA + ',' + indexInvA;
    let debugString = op + ':' + domain__debug(getDomain(indexR, true)) + '=' + domain__debug(getDomain(indexA, true)) + ',' + domain__debug(getDomain(indexB, true));

    let indexS = constraintHash[key];
    if (indexS === undefined) {
      let thisKey = op + ':' + indexA + ',' + indexB;
      TRACE(' - opposite for ' + op + ' (' + invOp + ') doesnt exist, adding this key then bailing');
      TRACE(' - checked for key=', key, ', now adding key:', thisKey);

      constraintHash[thisKey] = indexR;
      debugHash[thisKey] = debugString;

      return false;
    }

    TRACE(' - found the opposite of this constraint;');
    TRACE('    - #1:', debugHash[key]);
    TRACE('    - #2:', debugString);
    TRACE(' - indexR !^ indexS, and perhaps indexR == indexS, check that case first');

    ASSERT(argCount === 2, 'should have two args');

    let R = getDomain(indexR, true);
    if (domain_size(R) === 2 && !domain_hasNoZero(R) && R === getDomain(indexS, true)) {
      TRACE(' - indexR == indexS because', domain__debug(R), 'has two elements, one of them zero, and R==S');
      if (indexR === indexS) {
        TRACE(' - var is same so skipping alias');
      } else {
        addAlias(indexR, indexS);
      }
      ml_eliminate(ml, pc, SIZEOF_CR_2);
    } else {
      TRACE(' - indexR !^ indexS because R=', domain__debug(R), ', S=', domain__debug(getDomain(indexS, true)), '; R may still end up with a different value from S');
      TRACE(' - morphing to an xnor(R S);', ml_getOpSizeSlow(ml, pc), SIZEOF_C + 2 * 2 + 2);
      ASSERT(ml_getOpSizeSlow(ml, pc) >= (SIZEOF_C + 2 * 2 + 2), 'the current op should have at least the required space for a 2 arg xnor', ml_getOpSizeSlow(ml, pc));
      ml_cr2c2(ml, pc, argCount, ML_XNOR, indexR, indexS);
    }

    // dont update pc
    return true;
  }

  function innerLoop() {
    while (pc < ml.length && !emptyDomain) {
      ++__opCounter;
      let op = ml[pc];
      TRACE(' -- DD pc=' + pc + ', op: ' + ml__debug(ml, pc, 1, problem, true));
      switch (op) {
        case ML_IMP:
          dedupePairOc2('->');
          break;
        case ML_NIMP:
          dedupePairOc2('!->');
          break;

        case ML_ISLT:
          dedupeIsltIslte('<?');
          break;
        case ML_ISLTE:
          dedupeIsltIslte('<=?');
          break;

        case ML_ISALL:
          dedupeBoolyList('isall');
          break;
        case ML_ISDIFF:
          if (!dedupeInvIsSameIsDiff('isdiff')) dedupeBoolyList('isdiff');
          break;
        case ML_ISNALL:
          dedupeBoolyList('isnall');
          break;
        case ML_ISNONE:
          dedupeBoolyList('isnone');
          break;
        case ML_ISSAME:
          if (!dedupeInvIsSameIsDiff('issame')) dedupeBoolyList('issame');
          break;
        case ML_ISSOME:
          dedupeBoolyList('issome');
          break;

        case ML_ALL:
          dedupeVoidList('all');
          break;
        case ML_DIFF:
          dedupeVoidList('diff');
          break;
        case ML_LT:
          dedupePairOc2('<');
          break;
        case ML_LTE:
          dedupePairOc2('<=');
          break;
        case ML_NALL:
          dedupeVoidList('nall');
          break;
        case ML_NONE:
          dedupeVoidList('none');
          break;
        case ML_SAME:
          dedupeVoidList('same');
          break;
        case ML_SOME:
          dedupeVoidList('some');
          break;
        case ML_XNOR:
          dedupeVoidList('xnor');
          break;
        case ML_XOR:
          dedupeVoidList('^');
          break;

        case ML_MINUS:
          dedupeTripO('-');
          break;
        case ML_DIV:
          dedupeTripO('/');
          break;

        case ML_SUM:
          dedupeNonBoolyList('sum');
          break;
        case ML_PRODUCT:
          dedupeNonBoolyList('product');
          break;

        case ML_START:
          if (pc !== 0) {
            return ml_throw(ml, pc, 'deduper problem found START');
          }
          ++pc;
          break;

        case ML_STOP:
          return constraintHash;

        case ML_NOBOOL: // no deduping this!
        case ML_NOLEAF: // no deduping this!
          pc += SIZEOF_V;
          break;

        case ML_JMP:
          pc += SIZEOF_V + ml_dec16(ml, pc + 1);
          break;
        case ML_JMP32:
          pc += SIZEOF_W + ml_dec32(ml, pc + 1);
          break;

        case ML_NOOP:
          ++pc;
          break;
        case ML_NOOP2:
          pc += 2;
          break;
        case ML_NOOP3:
          pc += 3;
          break;
        case ML_NOOP4:
          pc += 4;
          break;

        default:
          ml_throw(ml, pc, '(dd) unknown op');
      }
    }
    if (!emptyDomain) ml_throw(ml, pc, '(dd) ML OOB');
  }
}

// BODY_STOP

export {
  deduper,
};
