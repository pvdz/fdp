// import dsl
// generate ml
// minimize -> reduce constraints
// generate propagators
// stabilize
// exit

import {
  $CHANGED,
  $REJECTED,
  $SOLVED,
  $STABLE,

  ASSERT,
  ASSERT_NORDOM,
  getTerm,
  INSPECT,
  setTerm,
  TRACE,
  THROW,
} from '../../fdlib/src/helpers';
import {
  domain__debug,
  domain_arrToSmallest,
  domain_containsValue,
  domain_createValue,
  domain_getValue,
  domain_intersection,
  domain_max,
  domain_middleElement,
  domain_min,
  domain_toArr,
} from '../../fdlib/src/domain';

import {
  ml_countConstraints,
  ml_getOpList,
  ml_hasConstraint,
} from './ml';
import {
  dsl2ml,
} from './dsl2ml';
import {
  ml2dsl,
} from './ml2dsl';
import {
  min_run,
} from './minimizer';
import {
  deduper,
} from './deduper';
import {
  cutter,
} from './cutter';
import {
  problem_create,
  //problem_from,
} from './problem';
import {
  bounty_collect,
} from './bounty';

// BODY_START

let FDP = {
  solve: fdpSolver,
};

/**
 * @param {string} dsl The input problem
 * @param {Function} solver The function to brute force the remainder of the problem after FDP reduces it, not called if already solved. Called with `solver(dsl, options)`.
 * @param {Object} fdpOptions
 * @property {boolean} [fdpOptions.singleCycle=false] Only do a single-nonloop minimization step before solving? Can be faster but sloppier.
 * @property {boolean} [fdpOptions.repeatUntilStable=true] Keep calling minimize/cutter per cycle until nothing changes?
 * @property {boolean} [fdpOptions.debugDsl=false] Enable debug output (adds lots of comments about vars)
 * @property {boolean} [fdpOptions.hashNames=true] Replace original varNames with `$<base36(index)>$` of their index in the output
 * @property {boolean} [fdpOptions.indexNames=false] Replace original varNames with `_<index>_` in the output
 * @property {boolean} [fdpOptions.groupedConstraints=true] When debugging only, add all constraints below a var decl where that var is used
 * @property {boolean} [fdpOptions.flattened=false] Solve all vars in the solution even if there are multiple open fdpOptions left
 * @property {boolean|Function} [fdpOptions.printDslBefore] Print the dsl after parsing it but before crunching it.
 * @property {boolean|Function} [fdpOptions.printDslAfter] Print the dsl after crunching it but before calling FD on it
 * @param {Object} solverOptions Passed on to the solver directly
 */
function fdpSolver(dsl, solver, fdpOptions = {}, solverOptions = {log: 1, vars: 'all'}) {
  ASSERT(typeof dsl === 'string');
  ASSERT(typeof fdpOptions !== 'function', 'confirming this isnt the old solver param');

  //fdpOptions.hashNames = false;
  //fdpOptions.repeatUntilStable = true;
  //fdpOptions.debugDsl = false;
  //fdpOptions.singleCycle = true;
  //fdpOptions.indexNames = true;
  //fdpOptions.groupedConstraints = true;

  if (solverOptions.logger) setTerm(solverOptions.logger);
  let term = getTerm();

  term.log('<pre>');
  term.time('</pre>');
  let r = _preSolver(dsl, solver, fdpOptions, solverOptions);
  term.timeEnd('</pre>');
  return r;
}
function _preSolver(dsl, solver, options, solveOptions) {
  ASSERT(typeof dsl === 'string');
  ASSERT(typeof options !== 'function', 'making sure this isnt the old Solver param');

  let term = getTerm();
  term.log('<pre-solving>');
  term.time('</pre-solving total>');
  let {
    hashNames = true,
    debugDsl = false,
    indexNames = false,
    groupedConstraints = true,
  } = options;
  if (options.hashNames === undefined) options.hashNames = hashNames;
  if (options.debugDsl === undefined) options.debugDsl = debugDsl;
  if (options.indexNames === undefined) options.indexNames = indexNames;
  if (options.groupedConstraints === undefined) options.groupedConstraints = groupedConstraints;

  let problem = problem_create();
  let {
    varNames,
    domains,
  } = problem;

  TRACE(dsl.slice(0, 1000) + (dsl.length > 1000 ? ' ... <trimmed>' : '') + '\n');

  let state = crunch(dsl, problem, options);

  let bounty;
  let betweenDsl;
  if (state === $REJECTED) {
    TRACE('Skipping ml2dsl because problem rejected and bounty/ml2dsl dont handle empty domains well');
  } else {
    term.time('ml->dsl');
    bounty = bounty_collect(problem.ml, problem);
    betweenDsl = ml2dsl(problem.ml, problem, bounty, {debugDsl: false, hashNames: true}); // use default generator settings for dsl to pass on to FD
    term.timeEnd('ml->dsl');
  }

  term.timeEnd('</pre-solving total>');
  if (state === $REJECTED) term.log('REJECTED');

  //term.log(domains.map((d,i) => i+':'+problem.targeted[i]).join(', '));
  // confirm domains has no gaps...
  //term.log(problem.domains)
  //for (let i=0; i<domains.length; ++i) {
  //  ASSERT(i in domains, 'no gaps');
  //  ASSERT(domains[i] !== undefined, 'no pseudo gaps');
  //}

  // cutter cant reject, only reduce. may eliminate the last standing constraints.
  let solution;
  if (state === $SOLVED || (state !== $REJECTED && !ml_hasConstraint(problem.ml))) {
    term.time('- generating early solution');
    solution = createSolution(problem, null, options, solveOptions.max || Infinity);
    term.timeEnd('- generating early solution');
  }

  if (state !== $REJECTED && ((betweenDsl && betweenDsl.length < 1000) || options.printDslAfter)) {
    let dslForLogging = ml2dsl(problem.ml, problem, bounty, options);
    let s = '\nResult dsl (debugDsl=' + debugDsl + ', hashNames=' + hashNames + ', indexNames=' + indexNames + '):\n' + dslForLogging;

    if (typeof options.printDslAfter === 'function') {
      options.printDslAfter(s);
    } else {
      term.log('#### <DSL> after crunching before FD');
      term.log(s);
      term.log('#### </DSL>');
    }
  }

  if (solution) {
    term.error('<solved without fdq>');
    return solution;
  }
  if (state === $REJECTED) {
    term.error('<rejected without fdq>');
    TRACE('problem rejected!');
    return false;
  }

  if (problem.input.varstrat === 'throw') {
    // the stats are for tests. dist will never even have this so this should be fine.
    // it's very difficult to ensure optimizations work properly otherwise
    ASSERT(false, `Forcing a choice with strat=throw; debug: ${varNames.length} vars, ${ml_countConstraints(problem.ml)} constraints, current domain state: ${domains.map((d, i) => i + ':' + varNames[i] + ':' + domain__debug(d).replace(/[a-z()\[\]]/g, '')).join(': ')} (${problem.leafs.length} leafs) ops: ${ml_getOpList(problem.ml)} #`);
    THROW('Forcing a choice with strat=throw');
  }

  term.error('\n\nSolving remaining problem through fdq now...');

  term.log('<FD>');
  term.time('</FD>');
  let fdSolution = solver(betweenDsl, solveOptions);
  term.timeEnd('</FD>');
  term.log('\n');

  // Now merge the results from fdSolution to construct the final solution
  // we need to map the vars from the dsl back to the original names.
  // "our" vars will be constructed like `$<hash>$` where the hash simply
  // means "our" var index as base36. So all we need to do is remove the
  // dollar signs and parseInt as base 36. Ignore all other vars as they
  // are temporary vars generated by fdq. We should not see them
  // anymore once we support targeted vars.

  term.log('fd result:', typeof fdSolution === 'string' ? fdSolution : 'SOLVED');

  TRACE('fdSolution = ', fdSolution ? Object.keys(fdSolution).length > 100 ? '<supressed; too big>' : fdSolution : 'REJECT');

  if (fdSolution && typeof fdSolution !== 'string') {
    term.error('<solved after fdq>');
    return createSolution(problem, fdSolution, options, solveOptions.max || Infinity);
  }

  term.error('<' + fdSolution + ' during fdq>');
  TRACE('problem rejected!');
  return false;
}

function crunch(dsl, problem, options = {}) {
  let {
    singleCycle = false,
    repeatUntilStable = true,
  } = options;

  let {
    varNames,
    domains,
    solveStack,
    $addVar,
    $getVar,
    $addAlias,
    $getAlias,
  } = problem;

  let term = getTerm();

  term.time('- dsl->ml');
  dsl2ml(dsl, problem);
  let ml = problem.ml;
  term.timeEnd('- dsl->ml');

  term.log('Parsed dsl (' + dsl.length + ' bytes) into ml (' + ml.length + ' bytes)');

  if (options.printDslBefore) {
    let bounty = bounty_collect(problem.ml, problem);
    let predsl = ml2dsl(ml, problem, bounty, options);
    if (typeof options.printDslBefore === 'function') {
      options.printDslBefore(predsl);
    } else {
      term.log('#### <DSL> after parsing before crunching');
      term.log(predsl);
      term.log('#### </DSL>');
    }
  }

  let state;
  if (singleCycle) { // only single cycle? usually most dramatic reduction. only runs a single loop of every step.
    term.time('- first minimizer cycle (single loop)');

    state = min_run(ml, problem, domains, varNames, true, !repeatUntilStable);
    term.timeEnd('- first minimizer cycle (single loop)');
    TRACE('First minimize pass result:', state);

    if (state !== $REJECTED) {
      term.time('- deduper cycle #');
      let deduperAddedAlias = deduper(ml, problem);
      term.timeEnd('- deduper cycle #');

      if (deduperAddedAlias >= 0) {
        term.time('- cutter cycle #');
        cutter(ml, problem, !repeatUntilStable);
        term.timeEnd('- cutter cycle #');
      }
    }
  } else { // multiple cycles? more expensive, may not be worth the gains
    let runLoops = 0;
    term.time('- all run cycles');
    do {
      TRACE('run loop...');
      state = run_cycle(ml, $getVar, $addVar, domains, varNames, $addAlias, $getAlias, solveStack, runLoops++, problem);
    } while (state === $CHANGED);
    term.timeEnd('- all run cycles');
  }

  return state;
}

function run_cycle(ml, getVar, addVar, domains, vars, addAlias, getAlias, solveStack, runLoops, problem) {
  let term = getTerm();
  term.time('- run_cycle #' + runLoops);

  term.time('- minimizer cycle #' + runLoops);
  let state = min_run(ml, problem, domains, vars, runLoops === 0);
  term.timeEnd('- minimizer cycle #' + runLoops);

  if (state === $SOLVED) return state;
  if (state === $REJECTED) return state;

  term.time('- deduper cycle #' + runLoops);
  let deduperAddedAlias = deduper(ml, problem);
  term.timeEnd('- deduper cycle #' + runLoops);

  if (deduperAddedAlias < 0) {
    state = $REJECTED;
  } else {
    term.time('- cutter cycle #' + runLoops);
    let cutLoops = cutter(ml, problem, false);
    term.timeEnd('- cutter cycle #' + runLoops);

    if (cutLoops > 1 || deduperAddedAlias) state = $CHANGED;
    else if (cutLoops < 0) state = $REJECTED;
    else {
      ASSERT(state === $CHANGED || state === $STABLE, 'minimize state should be either stable or changed here');
    }
  }

  term.timeEnd('- run_cycle #' + runLoops);
  return state;
}

function createSolution(problem, fdSolution, options, max) {
  getTerm().time('createSolution()');

  let {
    flattened = false,
  } = options;

  let {
    varNames,
    domains,
    solveStack,
    getAlias,
    targeted,
  } = problem;

  let _getDomainWithoutFd = problem.getDomain;
  let _setDomainWithoutFd = problem.setDomain;

  function getDomainFromSolverOrLocal(index, skipAliasCheck) {
    if (!skipAliasCheck) index = getAlias(index);

    if (fdSolution) {
      let key = '$' + index.toString(36) + '$';
      let fdval = fdSolution[key];
      if (typeof fdval === 'number') {
        return domain_createValue(fdval);
      } else if (fdval !== undefined) {
        ASSERT(fdval instanceof Array, 'expecting fdq to only create solutions as arrays or numbers', fdval);
        return domain_arrToSmallest(fdval);
      }
      // else the var was already solved by fd2 so just read from our local domains array
    }

    return _getDomainWithoutFd(index, true);
  }

  function setDomainInFdAndLocal(index, domain, skipAliasCheck, forPseudoAlias) {
    TRACE(' - solveStackSetDomain, index=', index, ', domain=', domain__debug(domain), ', skipAliasCheck=', skipAliasCheck, ', forPseudoAlias=', forPseudoAlias);
    ASSERT(domain, 'should not set an empty domain at this point');
    ASSERT(forPseudoAlias || domain_intersection(_getDomainWithoutFd(index), domain) === domain, 'should not introduce values into the domain that did not exist before unless for xnor pseudo-booly; current:', domain__debug(_getDomainWithoutFd(index)), ', updating to:', domain__debug(domain), 'varIndex:', index);

    if (!skipAliasCheck) index = getAlias(index);
    _setDomainWithoutFd(index, domain, true, false, forPseudoAlias);

    // update the FD result AND the local data structure to reflect this new domain
    // the FD value rules when checking intersection with the new domain
    // (but we can just use the getter abstraction here and overwrite regardless)

    if (fdSolution) {
      let key = '$' + index.toString(36) + '$';
      if (fdSolution[key] !== undefined) {
        let v = domain_getValue(domain);
        if (v >= 0) fdSolution[key] = v;
        else fdSolution[key] = domain_toArr(domain);
      }
    }
  }


  function force(varIndex, pseudoDomain) {
    ASSERT(typeof varIndex === 'number' && varIndex >= 0 && varIndex <= 0xffff, 'valid var to solve', varIndex);
    let finalVarIndex = getAlias(varIndex);
    let domain = getDomainFromSolverOrLocal(finalVarIndex, true); // NOTE: this will take from fdSolution if it contains a value, otherwise from local domains
    ASSERT_NORDOM(domain);
    ASSERT(pseudoDomain === undefined || domain_intersection(pseudoDomain, domain) === pseudoDomain, 'pseudoDomain should not introduce new values');

    let v = domain_getValue(domain);
    if (v < 0) {
      if (pseudoDomain) {
        TRACE('   - force() using pseudo domain', domain__debug(pseudoDomain), 'instead of actual domain', domain__debug(domain));
        domain = pseudoDomain;
      }
      TRACE('   - forcing index', varIndex, '(final index=', finalVarIndex, ') to min(' + domain__debug(domain) + '):', domain_min(domain));
      let dist = problem.valdist[varIndex];
      if (dist) {
        ASSERT(typeof dist === 'object', 'dist is an object');
        ASSERT(typeof dist.valtype === 'string', 'dist object should have a name'); // TODO: rename valtype to "name"? or maybe keep it this way because easier to search for anyways. *shrug*
        switch (dist.valtype) {
          case 'list':
            ASSERT(dist.list instanceof Array, 'lists should have a prio');
            dist.list.some(w => domain_containsValue(domain, w) && (v = w) >= 0);
            if (v < 0) v = domain_min(domain); // none of the prioritized values still exist so just pick one
            break;
          case 'max':
            v = domain_max(domain);
            break;
          case 'min':
          case 'naive':
            v = domain_min(domain);
            break;
          case 'mid':
            v = domain_middleElement(domain);
            break;
          case 'markov':
          case 'minMaxCycle':
          case 'splitMax':
          case 'splitMin':
            THROW('implement me (var mod) [' + dist.valtype + ']');
            v = domain_min(domain);
            break;
          default:
            THROW('Unknown dist name: [' + dist.valtype + ']', dist);
        }
      } else {
        // just an arbitrary choice then
        v = domain_min(domain);
      }

      ASSERT(domain_containsValue(domain, v), 'force() should not introduce new values');
      setDomainInFdAndLocal(varIndex, domain_createValue(v), true);
    }
    return v;
  }

  TRACE('\n# createSolution(), solveStack.length=', solveStack.length, ', using fdSolution?', !!fdSolution);
  TRACE(' - fdSolution:', domains.length < 50 ? INSPECT(fdSolution).replace(/\n/g, '') : '<big>');
  TRACE(' - domains:', domains.length < 50 ? domains.map((_, i) => '{index=' + i + ',name=' + problem.varNames[i] + ',' + domain__debug(problem.getDomain(i)) + '}').join(', ') : '<big>');

  ASSERT(domains.length < 50 || !void TRACE('domains before; index, unaliased, aliased, fdSolution (if any):\n', domains.map((d, i) => i + ': ' + domain__debug(d) + ', ' + domain__debug(_getDomainWithoutFd(i)) + ', ' + domain__debug(getDomainFromSolverOrLocal(i)))));

  function flushSolveStack() {
    TRACE('Flushing solve stack...', solveStack.length ? '' : ' and done! (solve stack was empty)');
    let rev = solveStack.reverse();
    for (let i = 0; i < rev.length; ++i) {
      let f = rev[i];
      TRACE('- solve stack entry', i);
      f(domains, force, getDomainFromSolverOrLocal, setDomainInFdAndLocal);

      TRACE(domains.length < 50 ? ' - domains now: ' + domains.map((_, i) => '{index=' + i + ',name=' + problem.varNames[i] + ',' + domain__debug(problem.getDomain(i)) + '}').join(', ') : '');
    }
    ASSERT(domains.length < 50 || !void TRACE('domains after solve stack flush; index, unaliased, aliased, fdSolution (if any):\n', domains.map((d, i) => i + ': ' + domain__debug(d) + ', ' + domain__debug(_getDomainWithoutFd(i)) + ', ' + domain__debug(getDomainFromSolverOrLocal(i)))));
  }
  flushSolveStack();

  ASSERT(!void domains.forEach((d, i) => ASSERT(domains[i] === false ? getAlias(i) !== i : ASSERT_NORDOM(d), 'domains should be aliased or nordom at this point', 'index=' + i, ', alias=', getAlias(i), ', domain=' + domain__debug(d), domains)));

  function flushValDists() {
    TRACE('\n# flushValDists: One last loop through all vars to force those with a valdist');
    for (let i = 0; i < domains.length; ++i) {
      if (flattened || problem.valdist[i]) {
        // can ignore FD here (I think)
        _setDomainWithoutFd(i, domain_createValue(force(i)), true);
      } else {
        // TOFIX: make this more efficient... (cache the domain somehow)
        let domain = getDomainFromSolverOrLocal(i);
        let v = domain_getValue(domain);
        if (v >= 0) {
          // can ignore FD here (I think)
          _setDomainWithoutFd(i, domain, true);
        }
      }
    }
  }
  flushValDists();
  TRACE('\n');

  ASSERT(domains.length < 50 || !void TRACE('domains after dist pops; index, unaliased, aliased, fdSolution (if any):\n', domains.map((d, i) => i + ': ' + domain__debug(d) + ', ' + domain__debug(_getDomainWithoutFd(i)) + ', ' + domain__debug(getDomainFromSolverOrLocal(i)))));
  ASSERT(!void domains.forEach((d, i) => ASSERT(d === false ? getAlias(i) !== i : (flattened ? domain_getValue(d) >= 0 : ASSERT_NORDOM(d)), 'domains should be aliased or nordom at this point', 'index=' + i, ', alias=', getAlias(i), 'domain=' + domain__debug(d), domains)));

  function flushAliases() {
    TRACE(' - syncing aliases');
    for (let i = 0; i < domains.length; ++i) {
      let d = domains[i];
      if (d === false) {
        let a = getAlias(i);
        let v = force(a);
        TRACE('Forcing', i, 'and', a, 'to be equal because they are aliased, resulting value=', v);
        // can ignore FD here (I think)
        _setDomainWithoutFd(i, domain_createValue(v), true);
      }
    }
  }
  flushAliases();

  ASSERT(domains.length < 50 || !void TRACE('domains after dealiasing; index, unaliased, aliased, fdSolution (if any):\n', domains.map((d, i) => i + ': ' + domain__debug(d) + ', ' + domain__debug(_getDomainWithoutFd(i)) + ', ' + domain__debug(getDomainFromSolverOrLocal(i)))));

  function generateFinalSolution() {
    TRACE(' - generating regular FINAL solution', flattened);
    let solution = {};
    for (let index = 0; index < varNames.length; ++index) {
      if (targeted[index]) {
        let name = varNames[index];
        let d = getDomainFromSolverOrLocal(index);
        let v = domain_getValue(d);
        if (v >= 0) {
          d = v;
        } else if (flattened) {
          ASSERT(!problem.valdist[index], 'only vars without valdist may not be solved at this point');
          d = domain_min(d);
        } else {
          d = domain_toArr(d);
        }
        solution[name] = d;
      }
    }
    return solution;
  }
  let solution = generateFinalSolution();

  getTerm().timeEnd('createSolution()');
  TRACE(' -> createSolution results in:', domains.length > 100 ? '<supressed; too many vars (' + domains.length + ')>' : solution);
  return solution;
}

// BODY_STOP

export default FDP;
