include "../node_modules/circomlib/circuits/bitify.circom";

template CasinoReturn() {
  signal input ticketPrice;
  signal input rng;
  signal output returnValue;

  component rngBits = Num2Bits(248);
  rngBits.in <== rng;

  var bitSum1 = 0;
  for (var i = 0; i < 128; i++) {
      bitSum1 += rngBits.out[i];
  }
  var bitSum2 = 0;
  for (var i = 0; i < 120; i++) {
      bitSum2 += rngBits.out[i + 100];
  }

  var jackPot = 0
  var e2 = 1;
  for (var i = 0; i < 20; i++) {
      jackPot += rngBits.out[i + 228] * e2;
      e2 = e2 + e2;
  }

  var out = (ticketPrice * (bitSum1 + bitSum2)) >> 8;

  if(jackPot > 2**20 - 10) {
      out = out + 5*ticketPrice;
  }

  returnValue <== out;
}
