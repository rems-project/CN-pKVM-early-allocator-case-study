predicate {} Byte (pointer p) {
  let B = Owned<char>(p);
  return {};
}

predicate {} ByteV (pointer p, integer the_value) {
  let B = Owned<char>(p);
  assert (B.value == the_value);
  return {};
}


predicate {} EarlyAlloc (pointer cur, integer end) {
  assert ((0 <= ((integer) cur)) && (((integer) cur) <= end));
  let R = 
    each(integer q; (((integer) cur) <= q) && (q <= (end - 1))) { 
      Byte((pointer)(((integer)((pointer) 0)) + (q*1))) 
  };
  return {};
}
