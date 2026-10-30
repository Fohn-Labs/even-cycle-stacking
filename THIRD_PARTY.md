# Existing work and dependency licenses

The graph-stacking definitions and the original conjecture are due to
Tamas Csernak and Lajos Soukup. Their two primary papers and repository are
linked in the README and proof references.

TreeStack supplies the existing Configuration, move, PebbleStep, Reach,
Stackable and F definitions used by the formalization. It is downloaded
at revision 4d4969703a9f0ca7a51cbe7edf0f0338cc95cafb from:

https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees

TreeStack is licensed under Apache-2.0. Its LICENSE remains in the downloaded
vendor directory. The setup script narrows the import lists in Transfer.lean
and PebblingMove.lean to fit the memory budget. It does not change their
definitions, theorem statements or proof bodies.

Lean and Mathlib are existing tools and libraries with their own licenses.
They are downloaded as pinned dependencies and are not relicensed by this
repository. The MIT license here applies to this session's original files.

The formalization's complete graph cases remain work in progress. Neither
the dependency authors nor any registration of their tree results is an
endorsement or certificate of this cycle argument.
