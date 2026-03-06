import Lean

-- These are the non terminals of our grammar.  They are declared independently of their rules
-- because they are "open": anyone can introduce new rules for these non terminals, or rewrite
-- rules on top of these.
declare_syntax_cat lustre_node
declare_syntax_cat lustre_expr
declare_syntax_cat lustre_node_decl
declare_syntax_cat lustre_assertion
declare_syntax_cat lustre_lower_bound
declare_syntax_cat lustre_upper_bound

-- These are the rules of our grammar.  A declaration of the form
--   syntax fragments : non-terminal
-- is written, in grammar style, as
--   non-terminal → fragments
-- Declarations preceded by a "sugar" comment indicate syntactic sugar.  They are folded to
-- non-sugar construction at the end of this file.
syntax lustre_ops := (ident ":=" ident),*
syntax (name := lustre_command) "lustre " ("(" lustre_ops ")")? lustre_node* : command
syntax "node " ident "(" ident,* ")" (" = " (ident),+)?
  (" guard" lustre_assertion*)? " where" lustre_node_decl*
  (" assert" lustre_assertion*)? : lustre_node

syntax ident,+ " = " lustre_expr : lustre_node_decl

syntax num : lustre_lower_bound
syntax "-∞" : lustre_lower_bound

syntax num : lustre_upper_bound
syntax "∞" : lustre_upper_bound

syntax:max "[" lustre_lower_bound ", " lustre_upper_bound "]" : lustre_expr
-- sugar
syntax:max num : lustre_expr
syntax:max ident : lustre_expr
syntax "-" lustre_expr : lustre_expr
syntax " pre " lustre_expr : lustre_expr
syntax:max " if " lustre_assertion:0 " then " lustre_expr:0 " else " lustre_expr:0 : lustre_expr
syntax:35 lustre_expr:36 " fby " lustre_expr:35 : lustre_expr
syntax:35 lustre_expr:36 " -> " lustre_expr:35 : lustre_expr
syntax:40 lustre_expr:40 " + " lustre_expr:41 : lustre_expr
syntax:40 lustre_expr:40 " - " lustre_expr:41 : lustre_expr
syntax:50 lustre_expr:50 " * " lustre_expr:51 : lustre_expr
syntax:60 ident "(" lustre_expr:0,* ")" : lustre_expr
syntax:max " if " lustre_assertion:0 " then " lustre_expr:0 " else " lustre_expr:0 : lustre_expr
macro:max " (" e:lustre_expr:0 ") " : lustre_expr => pure e

syntax:max lustre_expr " = " lustre_expr : lustre_assertion
-- sugar
syntax:max lustre_expr " ≠ " lustre_expr : lustre_assertion
syntax:max lustre_expr " ≤ " lustre_expr : lustre_assertion
syntax:max lustre_expr " < " lustre_expr : lustre_assertion
-- sugar
syntax:max lustre_expr " ≥ " lustre_expr : lustre_assertion
-- sugar
syntax:max lustre_expr " > " lustre_expr : lustre_assertion
syntax:50 lustre_assertion:50 " ∨ " lustre_assertion:51 : lustre_assertion
syntax:60 lustre_assertion:60 " ∧ " lustre_assertion:61 : lustre_assertion
-- sugar
syntax:65 " ¬" lustre_assertion:65 : lustre_assertion
-- sugar
syntax:max " (" lustre_assertion:0 ") " : lustre_assertion

-- Rewrite rules on top of the previously declared syntactic forms.
macro_rules
  | `(lustre_expr| $k:num) => `(lustre_expr| [$k:num, $k:num])
  | `(lustre_assertion| ¬ $e:lustre_assertion) => do
    match e with
    | `(lustre_assertion| $left ∨ $right) =>
      `(lustre_assertion| ¬$left ∧ ¬$right)
    | `(lustre_assertion| $left ∧ $right) =>
      `(lustre_assertion| ¬$left ∨ ¬$right)
    | `(lustre_assertion| $left:lustre_expr = $right) =>
      `(lustre_assertion| $left:lustre_expr ≠ $right)
    | `(lustre_assertion| $left:lustre_expr ≠ $right) =>
      `(lustre_assertion| $left:lustre_expr = $right)
    | `(lustre_assertion| $left:lustre_expr < $right) =>
      `(lustre_assertion| $left:lustre_expr ≥ $right)
    | `(lustre_assertion| $left:lustre_expr ≤ $right) =>
      `(lustre_assertion| $left:lustre_expr > $right)
    | `(lustre_assertion| $left:lustre_expr > $right) =>
      `(lustre_assertion| $left:lustre_expr ≤ $right)
    | `(lustre_assertion| $left:lustre_expr ≥ $right) =>
      `(lustre_assertion| $left:lustre_expr < $right)
    | `(lustre_assertion| ¬$b) =>
      `(lustre_assertion| $b)
    | _ => Lean.Macro.throwUnsupported
  | `(lustre_assertion| $left:lustre_expr ≠ $right:lustre_expr) =>
    `(lustre_assertion| $left:lustre_expr > $right ∨ $left:lustre_expr < $right)
  | `(lustre_assertion| $left:lustre_expr ≥ $right:lustre_expr) =>
    `(lustre_assertion| $right:lustre_expr ≤ $left)
  | `(lustre_assertion| $left:lustre_expr > $right:lustre_expr) =>
    `(lustre_assertion| $right:lustre_expr < $left)
  | `(lustre_assertion| ($e)) => pure e