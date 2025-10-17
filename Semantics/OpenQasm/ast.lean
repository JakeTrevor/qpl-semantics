import Lean
open Lean Elab Meta PrettyPrinter Delaborator SubExpr

namespace OpenQasm

structure RegisterRef where
  name : String
  idex : Nat

inductive Command where
  | CRegDecl          : String -> Nat -> Command
  | QRegDecl          : String -> Nat -> Command
  | GateApplication   : String -> List RegisterRef -> Command
  | Measure           : RegisterRef -> RegisterRef -> Command
  | IfStatement       : RegisterRef -> Command -> Command

inductive Program where
  | Done : Program
  | Then : Command -> Program -> Program


def extractStringLiteral (e : Expr) : DelabM String :=
  match e with
  | Expr.lit (Literal.strVal s) => return s
  | _ => failure

namespace RegisterRef

  declare_syntax_cat oqasm_reg_ref
  syntax ident "[" num "]" : oqasm_reg_ref

  partial def elaborate : Syntax → MetaM Expr
    | `(oqasm_reg_ref| $x:ident[$i:num]) =>
      mkAppM ``RegisterRef.mk #[Lean.mkStrLit x.getId.toString, mkNatLit i.getNat ]
    | _ => throwUnsupportedSyntax
  open RegisterRef


  def delab_inner (expr :Expr) : DelabM (TSyntax `oqasm_reg_ref) := do
    match_expr expr with
    | mk name idx =>
      let name := mkIdent <| .mkSimple <| ←extractStringLiteral name
      let idx := ⟨Syntax.mkNumLit (toString idx) |>.raw⟩
      `(oqasm_reg_ref| $name:ident[$idx])
    | _ => failure

  @[delab app.OpenQasm.RegisterRef.mk]
  def delab : Delab := do
    delab_inner (←getExpr) >>= fun x => pure ⟨ x.raw ⟩

  elab "regref" ppHardSpace "{" p:oqasm_reg_ref "}" : term => elaborate p
  #reduce regref { q[10] }
end RegisterRef


namespace Command
open Command

declare_syntax_cat oqasm_comm

declare_syntax_cat oqasm_prog
syntax(name:=oqasm_sequence) many(ppLine oqasm_comm) : oqasm_prog

syntax (name:= bit_decl) "bit" "["num"] " ident "; "                            : oqasm_comm
syntax (name:= qbit_decl) "qubit" "["num"] " ident "; "                         : oqasm_comm
syntax (name:= gate_app) ident sepBy(oqasm_reg_ref, ", ") "; "                  : oqasm_comm
syntax (name:= measure_stmt) oqasm_reg_ref " = " "measure " oqasm_reg_ref "; "  : oqasm_comm
syntax (name:= if_statement) "if" ppHardSpace "(" oqasm_reg_ref ")" ppHardSpace "{ " oqasm_prog ppDedent(ppLine " }") : oqasm_comm


partial def elaborate : Syntax -> MetaM Expr
  | `(bit_decl| bit [$n:num] $x:ident;) =>
    mkAppM ``CRegDecl #[mkStrLit x.getId.toString, mkNatLit n.getNat]

  | `(qbit_decl| qubit [$n:num] $x:ident;) =>
    mkAppM ``QRegDecl #[mkStrLit x.getId.toString, mkNatLit n.getNat]

  | `(gate_app| $g:ident $r:oqasm_reg_ref,*;)=> do
    let q <- r.getElems.mapM RegisterRef.elaborate
    let rs <- mkListLit (mkConst ``RegisterRef) q.toList
    mkAppM ``GateApplication #[mkStrLit g.getId.toString, rs]

  | `(measure_stmt| $c:oqasm_reg_ref = measure $r:oqasm_reg_ref;) => do
    let c' <- RegisterRef.elaborate c
    let r' <- RegisterRef.elaborate r
    mkAppM ``Measure #[c', r']

  | `(if_statement| if ($cond:oqasm_reg_ref) { $body:oqasm_comm } ) => do
    let cond <- RegisterRef.elaborate cond
    let body <- elaborate body
    mkAppM ``IfStatement #[cond, body]
  | _ => throwUnsupportedSyntax

elab "oqasm_command " "{ " c:oqasm_comm " }" : term => elaborate c

partial def delab_inner (expr : Expr): DelabM (TSyntax `oqasm_comm) := do
  match_expr expr with
    | CRegDecl name size =>
      let name := mkIdent <| .mkSimple <| ←extractStringLiteral name
      let size := ⟨Syntax.mkNumLit (toString size) |>.raw⟩
      `(oqasm_comm| bit[$size] $name;)

    | QRegDecl name size=> do
      let name := mkIdent <| .mkSimple <| ←extractStringLiteral name
      let size := ⟨Syntax.mkNumLit (toString size) |>.raw⟩
      `(oqasm_comm| qubit[$size] $name;)

    | GateApplication gate regs => do
        let gate := mkIdent <| .mkSimple <| ←extractStringLiteral gate
        match regs.listLit? with
        | .none => failure
        | .some (_, regs) =>
          let regs <- regs.mapM (RegisterRef.delab_inner)
          let regs := regs.toArray
          `(oqasm_comm| $gate:ident $(regs),*;)

    | Measure creg qreg => do
      let creg <- RegisterRef.delab_inner creg
      let qreg <- RegisterRef.delab_inner qreg
      `(oqasm_comm| $creg:oqasm_reg_ref = measure $qreg:oqasm_reg_ref; )

    | IfStatement creg body => do
      let creg <- RegisterRef.delab_inner creg
      let body <- delab_inner body
      `(oqasm_comm| if ($creg:oqasm_reg_ref) { $body:oqasm_comm }   )
    | _ => failure

@[delab app.OpenQasm.Command.CRegDecl, delab app.OpenQasm.Command.QRegDecl, delab app.OpenQasm.Command.GateApplication, delab app.OpenQasm.Command.Measure, delab app.OpenQasm.Command.IfStatement]
def delab : Delab := do
  let e <- getExpr
  guard <| match_expr e with
  | CRegDecl        _ _ => true
  | QRegDecl        _ _ => true
  | GateApplication _ _ => true
  | Measure         _ _ => true
  | IfStatement     _ _ => true
  | _ => false
  let stx <- delab_inner e
  `(term| oqasm_command { $stx })

#reduce oqasm_command { bit[1] x; }
#reduce oqasm_command { qubit[1] x; }
#reduce oqasm_command { H q[1], q[2]; }
#reduce oqasm_command { c[1] = measure q[1]; }
#reduce oqasm_command { if (c[1]) { bit[1] q; }}
end Command

namespace Program
open Program

def fromList : (cs : List Command) -> Program
  | [] => Done
  | (x :: xs) => Then x (fromList xs)

partial def elaborate : Syntax -> MetaM Expr
  | `(oqasm_prog| $comms:oqasm_comm* ) => do
    let comms <- comms.mapM (fun x => Command.elaborate (x.raw))
    let comms <- mkListLit (mkConst ``Command) comms.toList
    mkAppM ``Program.fromList #[comms]
  | _ => throwUnsupportedSyntax

elab "oqasm" ppHardSpace "{" p:oqasm_prog ppDedent(ppLine "}") : term => Program.elaborate p

partial def delab_listify (e : Expr) : DelabM (List Expr) := do
  match_expr e with
  | Done => return []
  | Then c rest => do
    let rest <- delab_listify rest
    return c :: rest
  | _ => failure

partial def delab_inner (commands : List Expr) : DelabM (TSyntax `oqasm_prog) := do
    let commands <- commands.mapM (Command.delab_inner)
    let commands := commands.toArray
    `(oqasm_prog| $[$commands]* )

@[delab app.OpenQasm.Program.Done, delab app.OpenQasm.Program.Then]
def delaborate : Delab := do
  let e <- getExpr
  guard <| match_expr e with
  | Done     => true
  | Then _ _ => true
  |      _   => false
  let epxrs <- delab_listify e
  let stx <- delab_inner epxrs
  `(term| oqasm { $stx } )
end Program



#reduce oqasm {
  bit[1] q;
}


#reduce oqasm {
  c[1] = measure q[1];
}

#reduce oqasm {
   H q[3];
}

#reduce oqasm {
  qubit[1] q;
  H q[0];
  c[1] = measure q[0];
}


#reduce oqasm {
  if (c[4]) {
    c[4] = measure q[2];
  }
}

#reduce oqasm { cx q[0], q[1]; }

def teleport := oqasm {
  bit[2] c;
  qubit[3] q;
  h q[1];
  cx q[1], q[2];
  cx q[0], q[1];
  h q[0];
  c[0] = measure q[0];
  c[1] = measure q[1];
  if (c[0]) {
    x q[2];
  }
  if (c[1]) {
    z q[2];
  }
}

#reduce teleport
