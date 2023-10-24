# logic

## TODO
- [ ] Make `True` and `False` a predicate
- [ ] Implement other equivalence
  - [ ] `p -> q` `==>` `~p | q`
  - [ ] Distributive Law: `a & (b | c)` `==>` `(a & c) | (b & c)`
  - [ ] Absorption Law: 
    - `a & (a | b)` `==>` `a`
    - `a | (a & b)` `==>` `a`
  - [ ] Identity Law: 
    - `True & a` `==>` `a`
    - `False | a` `==>` `a`
  - [ ] Null Law:
    - `False & a` `==>` `False`
    - `True | a` `==>` `True`
  - [ ] Idempotent Law:
    - `a & a` `==>` `a`
    - `a | a` `==>` `a`
  - [x] Complement:
    - `a & ~a` `==>` `False`
    - `a | ~a` `==>` `True`
  - [x] De'Morgan's Law
- [ ] Implement `simplify` function
- [ ] Implement "For All" and "There Exists"
- [ ] Implement Rules of Inference for "For All" and "There Exists"

## Notes
- `Statement.__eq__` should account for all equivalence.
- Create `show_equivalence` function, which create proof like object to show steps.