import ProofWidgets.Component.HtmlDisplay
import Lean

open Lean
open ProofWidgets.Jsx
open Elab.Command (CommandElabM liftCoreM)
open ProofWidgets ProofWidgets.HtmlEval ProofWidgets.HtmlCommand
open Lean.Server.RpcEncodable (rpcEncode)

def mkHtmlDotStx (ref : Syntax) (toDot : Std.Format) : Elab.Command.CommandElabM Unit := withRef ref do
  let url := "https://quickchart.io/graphviz?graph=" ++ (toDot.pretty /-|>.replace '\n' "" |>.replace ' ' ""-/)
  let img := Lean.mkIdent `img
  let src := Lean.mkIdent `src
  let html ← ``(<$img:ident $src:ident = {$(Syntax.mkStrLit url)} /-$(mkIdent `height):ident = "550"-/ />)
  let htX ← Elab.Command.liftTermElabM <| evalCommandMHtml <| ← ``(ProofWidgets.HtmlEval.eval $html)
  let ht ← htX
  liftCoreM <| Widget.savePanelWidgetInfo
      (hash HtmlDisplayPanel.javascript)
      (return json% { html: $(← rpcEncode ht) })
      ref
