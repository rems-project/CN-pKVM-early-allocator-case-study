predicate void Byte (pointer p) {
  take B = Owned<char>(p);
  return;
}

predicate void ByteV (pointer p, integer the_value) {
  take B = Owned<char>(p);
  assert (B == the_value);
  return;
}


predicate void EarlyAlloc (pointer cur, integer end) {
  assert ((0 <= ((integer) cur)) && (((integer) cur) <= end));
  take R = 
    each(integer q; ((integer) cur) <= q && q <= (end - 1)) { 
      Byte((pointer)(((integer)((pointer) 0)) + (q*1))) 
  };
  return;
}
