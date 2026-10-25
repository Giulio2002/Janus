val main : unit -> unit
function main() = {
  foreach (i from 0 to 255) {
    let v : bits(8) = get_slice_int(8, i, 0);
    print_int("probe ", probe(v)); print_int("onebit ", onebit(v));
    print_int("va ", va(v)); print_int("vd ", vd(v)); print_int("vg ", vg(v)); print_int("vh ", vh(v));
    print_int("vc ", vc(v)); print_int("ve ", ve(v));
    print_int("vb ", vb(v)); print_int("vf ", vf(v)); print_int("vcat ", vcat(v))
  };
  print_int("rtz ", rtz(18446744073709551615, 7));
  print_int("rtz ", rtz(-9223372036854775808, -1));
  print_int("rtz ", rtz(-9223372036854775807, 3));
  print_int("rtz ", rtz(18446744073709551557, 18446744073709551533));
  print_int("rtz ", rtz(-7, 2));
  print_int("rtz ", rtz(7, -2));
  print_int("rtz ", rtz(1234567890123456789012345, 97));
  print_int("rpow ", rpow(2, -3));
  print_int("rpow ", rpow(3, 5));
  print_int("rpow ", rpow(-2, -1));
  print_int("rsq ", rsq(4, 1));
  print_int("rsq ", rsq(9, 4));
  print_int("rsq ", rsq(2, 1));
  print_int("rsq ", rsq(1, 2));
  print_int("rsq ", rsq(1, 3));
  print_int("rsq ", rsq(100000000000000000001, 1));
  print_int("rsq ", rsq(1000000000000000000000000000000, 7));
  print_int("rsq ", rsq(1, 10000000000000000000000000));
  print_int("rsq ", rsq(1, 1267650600228229401496703205376));
  print_int("rsq ", rsq(3, 2535301200456458802993406410752));
  print_int("rsq ", rsq(1606938044258990275541962092341162602522202993782792835301377, 1));
  print_int("rsq ", rsq(123456789, 1000));
  print_int("rsq ", rsq(5, 1));
  print_int("rsq ", rsq(7, 3));
  print_int("rsq ", rsq(144, 25));
  print_int("rsq ", rsq(1, 1));
  print_int("rsq ", rsq(99, 100));
  print_int("rsq ", rsq(4503599627370497, 4503599627370496));
  print_int("rsq ", rsq(81129638414606681695789005144065, 81129638414606681695789005144064));
  print_int("rsq ", rsq(17, 1));
  print_int("rsq ", rsq(1, 10000000000000000000000000000000000000000));
  print_int("rsq ", rsq(31415926535, 10000000000));
  print_int("rsq ", rsq(999999999999999999, 1000000000000000000));
  print_int("rsq ", rsq(2, 12157665459056928801));
  print_int("rsq ", rsq(221073919720733357899776, 1));
  print_int("rsq ", rsq(221073919720733357899777, 1));
  print_int("rsq ", rsq(3, 4));
  print_int("rsq ", rsq(1, 4));
  print_int("rsq ", rsq(1152921504606846976, 3));
  print_int("rsq ", rsq(100000000000000000000000000000000000000000000000007, 13))
}
