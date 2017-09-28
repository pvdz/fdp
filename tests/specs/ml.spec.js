import expect from '../../../fdlib/tests/lib/mocha_proxy.fixt';

import {
  ML_LTE,
  ML_JMP,
  ML_START,
  ML_STOP,

  ml_enc8,
  ml_enc16,
  ml_getRecycleOffset,
  _ml_heapSort16bitInline,
  ml_recycleVV,
} from '../../src/ml';

describe('fdp/ml.spec', function() {

  describe('ml_heapSort16bitInline', function() {

    it('should work with empty buffer', function() {
      let buf = new Uint8Array(0);
      _ml_heapSort16bitInline(buf, 0, 0);

      expect(buf).to.eql(new Uint8Array(0));
    });

    it('should work with empty list', function() {
      let buf = new Uint8Array(Buffer.from('foobar', 'binary'));
      _ml_heapSort16bitInline(buf, 0, 0);

      expect(buf).to.eql(new Uint8Array(Buffer.from('foobar', 'binary'))); // [ar, fo, ob], unchanged because len=0
    });

    it('should sort the foobar', function() {
      let buf = new Uint8Array(Buffer.from('foobar', 'binary'));
      _ml_heapSort16bitInline(buf, 0, 3);

      expect(buf).to.eql(new Uint8Array(Buffer.from('arfoob', 'binary'))); // [ar, fo, ob]
    });

    it('should sort the foobar offset 1 till end', function() {
      let buf = new Uint8Array(Buffer.from('\xfffoobar', 'binary'));
      _ml_heapSort16bitInline(buf, 1, 3);

      expect(buf).to.eql(new Uint8Array(Buffer.from('\xffarfoob', 'binary'))); // [255, ar, fo, ob]
    });

    it('should sort the foobar offset 1 with suffix', function() {
      let buf = new Uint8Array(Buffer.from('\xfffoobar\xfe', 'binary'));
      _ml_heapSort16bitInline(buf, 1, 3);

      expect(buf).to.eql(new Uint8Array(Buffer.from('\xffarfoob\xfe', 'binary'))); // [255, ar, fo, ob, 254]
    });

    it('should sort the sum args in this regression', function() {
      let buf = new Uint8Array(Buffer.from('\x18\x20\x17\x9b\x17\x62\x17\xc1\x17\xe7\x17\xfa\x17\x75\x17\x88', 'binary'));
      _ml_heapSort16bitInline(buf, 0, 8);

      expect(buf).to.eql(new Uint8Array(Buffer.from('\x17\x62\x17\x75\x17\x88\x17\x9b\x17\xc1\x17\xe7\x17\xfa\x18\x20', 'binary')));
    });

    it('should not copy child value to parent value in heap sort', function() {
      let buf = new Uint8Array(Buffer.from('\x00\x06\x00\x03\x00\x01\x00\x04\x00\x05\x00\x02', 'binary'));
      _ml_heapSort16bitInline(buf, 0, 6);

      // it's mainly testing a a regression
      expect(buf).to.eql(new Uint8Array(Buffer.from('\x00\x01\x00\x02\x00\x03\x00\x04\x00\x05\x00\x06', 'binary')));
    });
  });

  describe('recycle', function() {

    it('should get an empty offset of exact requested size', function() {
      let ml = new Uint8Array(7);
      ml_enc8(ml, 0, ML_START);
      ml_enc8(ml, 1, ML_JMP);
      ml_enc16(ml, 2, 2);
      ml_enc8(ml, 6, ML_STOP);
      let offset = ml_getRecycleOffset(ml, 0, 5);

      // note: the first will be considered ML_START so the next will be targeted
      expect(offset).to.eql(1);
    });

    it('should get an empty offset even if its bigger', function() {
      let ml = new Uint8Array(7);
      ml_enc8(ml, 0, ML_START);
      ml_enc8(ml, 1, ML_JMP);
      ml_enc16(ml, 2, 2);
      ml_enc8(ml, 6, ML_STOP);
      let offset = ml_getRecycleOffset(ml, 0, 5);

      // note: the first will be considered ML_START so the next will be targeted
      expect(offset).to.eql(1);
    });

    it('should fail if there is no empty offset', function() {
      let ml = new Uint8Array(10);
      ml_enc8(ml, 0, ML_START);
      ml_enc8(ml, 1, ML_JMP);
      ml_enc16(ml, 2, 5);
      ml_enc8(ml, 9, ML_STOP);
      let offset = ml_getRecycleOffset(ml, 0, 9);

      // since the first viable offset would be pos=1 and that only has 9 spaces, the search should fail
      expect(offset).to.eql(undefined);
    });

    it('should skip an offset if its too small and still return the next one if its big enough', function() {
      let ml = new Uint8Array(30);
      ml_enc8(ml, 0, ML_START);
      ml_enc8(ml, 1, ML_JMP);
      ml_enc16(ml, 2, 5);
      ml_enc8(ml, 9, ML_JMP);
      ml_enc16(ml, 10, 18);
      ml_enc8(ml, 29, ML_STOP);
      let offset = ml_getRecycleOffset(ml, 0, 9);

      // since the first viable offset would be pos=1 and that only has 9 spaces, the search should fail
      expect(offset).to.eql(9);
    });
  });

  describe('ml_recycleVV', function() {

    // dunno whether to keep this test at all
    it.skip('should compile an lte', function() {
      let init = new Uint8Array(30);
      init.fill(0);
      ml_enc8(init, 0, ML_START);
      ml_enc8(init, 1, ML_JMP);
      ml_enc16(init, 2, 5);
      ml_enc8(init, 9, ML_JMP);
      ml_enc16(init, 10, 17);
      ml_enc8(init, 29, ML_STOP);

      // the recycle should get the second jump (len=3+17), then use that to compile in a LTE (len=5) and a jump for the remaining space (len=3+12)
      let expected = new Uint8Array(Buffer.from(init));
      ml_enc8(expected, 9, ML_LTE);
      ml_enc16(expected, 10, 1);
      ml_enc16(expected, 12, 2);
      ml_enc8(expected, 14, ML_JMP);
      ml_enc16(expected, 15, 12);

      //console.log('------ start');
      let ml = new Uint8Array(Buffer.from(init));
      let offset = ml_getRecycleOffset(ml, 0, 9);
      ml_recycleVV(ml, offset, ML_LTE, 1, 2);

      //console.log('');
      //console.log('init:', init);
      //console.log('have:', ml);
      //console.log('want:', expected);

      // since the first viable offset would be pos=1 and that only has 9 spaces, the search should fail
      expect(ml).to.eql(expected);
    });

    // dunno whether to keep this test at all
    it.skip('should compile two ltes', function() {
      let init = new Uint8Array(30);
      init.fill(0);
      ml_enc8(init, 0, ML_START);
      ml_enc8(init, 1, ML_JMP);
      ml_enc16(init, 2, 5);
      ml_enc8(init, 9, ML_JMP);
      ml_enc16(init, 10, 17);
      ml_enc8(init, 29, ML_STOP);

      // the recycle should get the second jump (len=3+17), then use that to compile in a LTE (len=5) and a jump for the remaining space (len=3+12)
      let expected = new Uint8Array(Buffer.from(init));
      ml_enc8(expected, 9, ML_LTE);
      ml_enc16(expected, 10, 1);
      ml_enc16(expected, 12, 2);
      ml_enc8(expected, 14, ML_LTE);
      ml_enc16(expected, 15, 1);
      ml_enc16(expected, 17, 2);
      ml_enc8(expected, 19, ML_JMP);
      ml_enc16(expected, 20, 7);

      //console.log('------ start');
      let ml = new Uint8Array(Buffer.from(init));
      let offset = ml_getRecycleOffset(ml, 0, 9);
      ml_recycleVV(ml, offset, ML_LTE, 1, 2);
      ml_recycleVV(ml, offset + 5, ML_LTE, 1, 2);

      //console.log('');
      //console.log('init:', init);
      //console.log('have:', ml);
      //console.log('want:', expected);

      // since the first viable offset would be pos=1 and that only has 9 spaces, the search should fail
      expect(ml).to.eql(expected);
    });
  });
});
