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
  print_int("rpow ", rpow(-2, -1))
}
