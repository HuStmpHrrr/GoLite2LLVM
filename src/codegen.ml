open Typed
include Cg_common

let codegen_program (p : program) : cgenv =
  let g = new_cgenv p.pkg_decl.data in
  let module C = Cg_tdecl.Make (struct let g = g end) in
  begin
    try
      List.iter C.codegen_top_decl p.top_decls;
      C.codegen_main p.top_decls
    with BrokenFunction _ ->
          ()
  end;
  match Llvm_analysis.verify_module g.cgmod with
  | None   -> g
  | Some s -> 
    raise (BrokenModule (s, string_of_llmodule g.cgmod))
