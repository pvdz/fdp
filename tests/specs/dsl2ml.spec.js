import expect from '../../../fdlib/tests/lib/mocha_proxy.fixt';

import FDO from '../../../fdo/src/fdo';
import FDP from '../../src/fdp';

describe('fdp//dsl2ml.spec', function() {

  it('should only return results asked for', function() {
    expect(FDP.solve(`
      : A [0 0 2 2 5 5]
      : B [0 10]
      : C [0 1]
      A = B + C
      @custom targets(B)
    `, FDO.solve)).to.eql({B: 0}); // point is to only report var B, actual outcome irrelevant
  });
});
