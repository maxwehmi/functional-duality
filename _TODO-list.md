<!--- To check of an item, add fill in the box with "x", like so [x]  :)--->
# General:
- [ ] Write comments / documentation
- [ ] Figure out how to use type constructors
  - [ ] make a type for posets which only works if the ordered set is actually reflexive, transitive and anti-symmetric
  - [ ] make a type for distributive bounded lattices which only works if the order is actually a distributive bounded lattice
  - [ ] make a type for Priestley Space which only works if the space is actually a topological space and satisfies the PSA
  
  
## Poset:
- [x] Write a function which checks if a given Ordered Set is a Poset, i.e. reflexive, transitive and anti-symmetric
- [x] Write a function makes a Ordered Set into a Poset by taking the reflexive transitive closure (and throws an
    error if the Relation is not anti-symmetric)
  - [ ] alternative function that forces anti-symmetery. Current idea is to, for any symmetric pair, take out both.
- [ ] write a check whether to the check the relation does not contain any elements not in the underlying set of our poset.

## DL: 
- [ ] Write a function which checks if a given Ordered Set forms a lattice, i.e. has meets and joins
- [x] Write a function which checks if a given Lattice is bounded
- [x] Write a function which checks if a given Lattice is distributive
- [ ] Write a function which converts a Poset into a lattice (if it has meets and joins)

## PS: 
- [ ] Write a function which checks if a given ordered "TopoSpace" is a Priestley Space
- [x] Write a function which checks if a given ordered topological spaces satisfies the Priestley Seperation axiom
- [ ] Write a function which checks if a "TopoSpace" is actually a topological space 
- potentially: prove `mapTop mapping ta == tb` to be put in the report


# Later:
- [ ] Write a function to pretty print posets
- [ ] Write a translation function from a DL to a PS
- [ ] Write a translation function from a PS to a DL 
- [ ] Write arbitrary instances for DL
- [ ] Write arbitrary instances for PS
- [ ] Write a function which checks for two given DL if there is an isomorphism between them (or should the iso be given?)
- [ ] Write a function which checks for two given PS if there is an isomorphism between them (or should the iso be given?)

## Possible Extensions:
- [ ] Generate minimal Priestley Space from a given Set
- [ ] Dualize morphisms between DL/PS to PS/DL
- [ ] calculate subdirectly irreducible subalgebras of a given algebra
- [ ] pretty Show intsances(?)
