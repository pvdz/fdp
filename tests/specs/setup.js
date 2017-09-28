// set up verifier to work as intended
// the tests in fdv should run after this script

import FDP from '../../src/fdp';
import FDO from '../../../fdo/src/fdo';
import {
  setSolver,
} from '../../../fdv/verifier';

setSolver((dsl, fdpOptions, fdoOptions) => FDP.solve(dsl, FDO.solve, fdpOptions, fdoOptions));
