// "Lowers" Prepared AST with Resolver-Data to "High-IR"
//   which is a CFG of basic blocks with SSA and more ops done

// steps TODO:
// 1. clean CFG building
// 2. with it: SSA with Cytron(https://dl.acm.org/doi/pdf/10.1145/115372.115320)
//          or Braun(https://link.springer.com/content/pdf/10.1007/978-3-642-37051-9_6.pdf)
// 3. with it: Local Value Numbering
