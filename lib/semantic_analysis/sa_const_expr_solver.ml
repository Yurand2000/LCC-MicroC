open Ast

(* Helper function *)
let annotate node loc = { node = node; loc = loc }

(* Main Solver Function *)
let rec solve_const_expressions program =
    let topdecls = match program with
    | Prog(topdecls) -> topdecls
    in
    let solve_gvar_decl topdecl =
        let loc = topdecl.loc in
        let topdecl = match topdecl.node with
            | Vardec(typ, id, expr) -> solve_global_variable typ id expr
            | _ -> topdecl.node
        in
        annotate topdecl loc
    in
    let solve_fn_bodies topdecl =
        let loc = topdecl.loc in
        let topdecl =
            match topdecl.node with
            | Fundecl(decl) -> solve_function_definition decl
            | _ -> topdecl.node
        in
        annotate topdecl loc
    in
    let topdecls = List.map solve_gvar_decl topdecls in
    let topdecls = List.map solve_fn_bodies topdecls in
    Prog(topdecls)

and solve_global_variable typ id expr =
    Vardec (typ, id, Option.map solve_expr expr)

and solve_function_definition { typ=typ; fname=fname; formals=formals; body=body; } =
    Fundecl { typ=typ; fname=fname; formals=formals; body=solve_stmt body; }

and solve_stmt stmt =
    let loc = stmt.loc in
    let stmt = match stmt.node with
    | If(guard, t_branch, e_branch) -> If(solve_expr guard, solve_stmt t_branch, solve_stmt e_branch)
    | While(guard, body) -> While(solve_expr guard, solve_stmt body)
    | Expr(expr) -> Expr(solve_expr expr)
    | Return(Some(expr)) -> Return(Some(solve_expr expr))
    | Block(stmts) -> Block(List.map solve_stmt_or_decl stmts)
    | _ -> stmt.node
    in
    annotate stmt loc     

and solve_stmt_or_decl stmt_or_decl =
    let loc = stmt_or_decl.loc in
    let stmt_or_decl = match stmt_or_decl.node with
        | Dec(_) -> stmt_or_decl.node
        | Stmt(stmt) -> Stmt(solve_stmt stmt)
    in
    annotate stmt_or_decl loc

and solve_expr expr =
    let loc = expr.loc in
    let new_expr = match expr.node with
    | Access(_) -> expr.node
    | Assign(access, expr) -> Assign(access, solve_expr expr)
    | Addr(_) -> expr.node
    | ILiteral(_) | FLiteral(_)
    | CLiteral(_) | BLiteral(_)
    | SLiteral(_)
    | SizeOf(_) -> expr.node
    | UnaryOp(op, expr) -> solve_unary_op_expr op expr
    | BinaryOp(op, lexpr, rexpr) -> solve_binary_op_expr op lexpr rexpr
    | CommaOp(lexpr, rexpr) -> CommaOp(solve_expr lexpr, solve_expr rexpr)
    | Call(id, args) -> Call(id, List.map solve_expr args)
    | Cast(typ, expr) -> solve_cast_expr typ expr
    in
    annotate new_expr loc

and solve_unary_op_expr op expr =
    let expr = solve_expr expr in
    match (op, expr.node) with
    | (Pos, _) -> expr.node
    | (Neg, ILiteral(value)) -> ILiteral(- value)
    | (Neg, FLiteral(value)) -> FLiteral(-. value)
    | (Bit_Not, ILiteral(value)) -> ILiteral(Int.lognot value)
    | (Not, BLiteral(value)) -> BLiteral(Bool.not value)
    | _ -> UnaryOp(op, expr)

and solve_binary_op_expr op lexpr rexpr =
    let lexpr = solve_expr lexpr in
    let rexpr = solve_expr rexpr in
    match (op, lexpr.node, rexpr.node) with
    | (Add, ILiteral(lvalue), ILiteral(rvalue)) -> ILiteral(lvalue + rvalue)
    | (Add, FLiteral(lvalue), FLiteral(rvalue)) -> FLiteral(lvalue +. rvalue)
    | (Sub, ILiteral(lvalue), ILiteral(rvalue)) -> ILiteral(lvalue - rvalue)
    | (Sub, FLiteral(lvalue), FLiteral(rvalue)) -> FLiteral(lvalue -. rvalue)
    | (Mult, ILiteral(lvalue), ILiteral(rvalue)) -> ILiteral(lvalue * rvalue)
    | (Mult, FLiteral(lvalue), FLiteral(rvalue)) -> FLiteral(lvalue *. rvalue)
    | (Div, ILiteral(lvalue), ILiteral(rvalue)) -> ILiteral(lvalue / rvalue)
    | (Div, FLiteral(lvalue), FLiteral(rvalue)) -> FLiteral(lvalue /. rvalue)
    | (Mod, ILiteral(lvalue), ILiteral(rvalue)) -> ILiteral(lvalue mod rvalue)

    | (Bit_And, ILiteral(lvalue), ILiteral(rvalue)) -> ILiteral(Int.logand lvalue rvalue)
    | (Bit_Or, ILiteral(lvalue), ILiteral(rvalue)) -> ILiteral(Int.logor lvalue rvalue)
    | (Bit_Xor, ILiteral(lvalue), ILiteral(rvalue)) -> ILiteral(Int.logxor lvalue rvalue)
    | (Shift_Left, ILiteral(lvalue), ILiteral(rvalue)) -> ILiteral(Int.shift_left lvalue rvalue)
    | (Shift_Right, ILiteral(lvalue), ILiteral(rvalue)) -> ILiteral(Int.shift_right lvalue rvalue)

    | (And, BLiteral(lvalue), BLiteral(rvalue)) -> BLiteral(lvalue && rvalue)
    | (Or, BLiteral(lvalue), BLiteral(rvalue)) -> BLiteral(lvalue || rvalue)

    | (Equal, BLiteral(lvalue), BLiteral(rvalue)) -> BLiteral(lvalue = rvalue)
    | (Equal, ILiteral(lvalue), ILiteral(rvalue)) -> BLiteral(lvalue = rvalue)
    | (Equal, CLiteral(lvalue), CLiteral(rvalue)) -> BLiteral(lvalue = rvalue)
    | (Equal, FLiteral(lvalue), FLiteral(rvalue)) -> BLiteral(lvalue = rvalue)
    | (Neq, BLiteral(lvalue), BLiteral(rvalue)) -> BLiteral(lvalue != rvalue)
    | (Neq, ILiteral(lvalue), ILiteral(rvalue)) -> BLiteral(lvalue != rvalue)
    | (Neq, CLiteral(lvalue), CLiteral(rvalue)) -> BLiteral(lvalue != rvalue)
    | (Neq, FLiteral(lvalue), FLiteral(rvalue)) -> BLiteral(lvalue != rvalue)

    | (Less, ILiteral(lvalue), ILiteral(rvalue)) -> BLiteral(lvalue < rvalue)
    | (Less, FLiteral(lvalue), FLiteral(rvalue)) -> BLiteral(lvalue < rvalue)
    | (Leq, ILiteral(lvalue), ILiteral(rvalue)) -> BLiteral(lvalue <= rvalue)
    | (Leq, FLiteral(lvalue), FLiteral(rvalue)) -> BLiteral(lvalue <= rvalue)
    | (Greater, ILiteral(lvalue), ILiteral(rvalue)) -> BLiteral(lvalue > rvalue)
    | (Greater, FLiteral(lvalue), FLiteral(rvalue)) -> BLiteral(lvalue > rvalue)
    | (Geq, ILiteral(lvalue), ILiteral(rvalue)) -> BLiteral(lvalue >= rvalue)
    | (Geq, FLiteral(lvalue), FLiteral(rvalue)) -> BLiteral(lvalue >= rvalue)

    | _ -> BinaryOp(op, lexpr, rexpr)

and solve_cast_expr typ expr =
    let expr = solve_expr expr in
    match (typ, expr.node) with
    | (Ast.TypI, FLiteral(value)) -> ILiteral(Int.of_float value)
    | (Ast.TypF, ILiteral(value)) -> FLiteral(Int.to_float value)
    | _ -> Cast(typ, expr)