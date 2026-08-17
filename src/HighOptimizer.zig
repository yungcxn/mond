// 1. CFG Simplification
// 2. Scalar Replacement of Aggregates
// 3. InstCombine + local CSE (fused, one worklist pass) - algebraic simplify and merge
// 4. Inlining
// 5. Sparse Conditional Constant Propagation - (AI says: subsumes plain constant folding and unreachable-branch elimination in one dataflow pass)
// 6. Global value numbering (across block value dedupe)
// 7. Dead Store Elimination with local alias analysis
// 8. Jump Threading
// 9. Loop Pass Group: LICM -> loop rotate -> induction-variable simplification/strength reduction -> unrolling (small trip counts) -> SLP + loop vectorization
// 10. Tail-Call Elim
// 11. Final Dead Code Killing
