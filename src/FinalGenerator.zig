// AI suggests:
//   Peephole/InstCombine pass again, now over lowered address arithmetic (folds redundant offset computation the ABI lowering introduced)
//   Redundant load/store elimination post-lowering (ABI expansion often creates them)
//   Block layout / hot-cold splitting for fallthrough and I-cache locality,  heuristic-based without profile data, profile-guided if available
//   Final DCE
