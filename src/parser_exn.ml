open Ast
open Meta

exception ShortDeclIdents of expr

exception NotFuncApplication of expr

exception AtMostOneDefault of unit meta

exception ForPostNoShortDecl of simp_stmt
