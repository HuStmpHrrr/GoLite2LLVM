open Meta

type arith =
  | Plus | Minus | Times | Div | Rem
  | Band | Bor | Bxor | Lshift | Rshift | Bclear (* bit clear (AND NOT) *)

type logic =
  | And | Or
  | Eq | Neq | Ge | Le | Gt | Lt
   
type binop =
  | Ar of arith
  | Lo of logic

type uniop =
  | Pos | Neg | Not
  | Bcomp                       (* ^x bitwise complement *)
  (* | Addr                        (\* &x *\)
   * | Indir                       (\* *x *\)
   * | Rec                         (\* <- x *\) *)

type bol =
  | True | False
  
type 'a gname =
  | Blank
  | X of 'a

type name = string gname

type lname = int gname
       
exception ContinueMustInLoopOrSwitch of unit meta
exception BreakMustInLoop of unit meta
