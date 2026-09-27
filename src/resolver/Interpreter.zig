// this is owned by `Resolver` as we do not emit high-IR with comptime code -> everything comptime
//   is executed in resolving stage

// to know when to really stop possibly infinite loops
step_budget: u32,
