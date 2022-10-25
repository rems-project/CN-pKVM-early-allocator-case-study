/*@ lemma_auto void characters_zeroed_join(char *array);
    requires [?f]characters_zeroed(array, ?n) &*& [f]characters_zeroed(array + n, ?n0);
    ensures [f]characters_zeroed(array, n + n0); @*/
