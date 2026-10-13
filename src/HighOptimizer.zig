// planned passes over `HighIr`, in order:
// 1. cfg simplification
// 2. scalar replacement of aggregates
// 3. instcombine with local cse, one worklist pass
// 4. inlining
// 5. sparse conditional constant propagation, which also drops unreachable branches
// 6. global value numbering across blocks
// 7. dead store elimination with local alias analysis
// 8. jump threading
// 9. loops: licm, rotation, induction variables, unrolling, vectorization
// 10. tail call elimination
// 11. dead code elimination
