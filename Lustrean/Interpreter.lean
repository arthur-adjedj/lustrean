import Lustrean.Imp
import Lustrean.Domain
import Misc.Lean

namespace Lustrean
structure Node (nb_var nb_arcs : Nat) : Type where
  in_nodes : List (Fin nb_arcs)
  deriving Repr

structure Arc (nb_var nb_nodes : Nat) : Type where
  src : Fin nb_nodes
  dst : Fin nb_nodes
  inst : Instruction nb_var
  ref? : Option Lean.Syntax
  deriving Repr

namespace Arc
variable {nb_var nb_nodes : Nat}
protected def toString (self : Arc nb_var nb_nodes) : String :=
  s!"({self.src} -> {self.dst} / {self.inst})"

instance : ToString (Arc nb_var nb_nodes) where
  toString := Arc.toString
end Arc

structure Cfg (nb_var : Nat) : Type where
  nb_nodes : Nat
  nb_arcs : Nat
  nodes : Array (Node nb_var nb_arcs)
  Hnodes : nb_nodes = nodes.size
  arcs : Array (Arc nb_var nb_nodes)
  Harcs : nb_arcs = arcs.size
  deriving Repr

namespace Cfg
variable {nb_var : Nat}

  namespace new
variable (nb_nodes nb_arcs : Nat)

def findNbArcs (l : List (PreNode nb_var)) : Nat :=
  List.foldl (fun n pn => n + pn.out_nodes.length) 0 l

theorem find_nb_arcs_incr : ∀ (l : List (PreNode nb_var)) (n m : Nat),
  n ≤ m →
  List.foldl (fun n pn => n + pn.out_nodes.length) n l ≤
    List.foldl (fun n pn => n + pn.out_nodes.length) m l
:= by
  intros l n m H
  induction l generalizing n m with
  | nil => assumption
  | cons _ _ IH =>
    apply IH
    simp
    assumption

theorem find_nb_arcs_add : ∀ (l : List (PreNode nb_var)) (n m : Nat),
  List.foldl (fun n pn => n + pn.out_nodes.length) n l + m
    = List.foldl (fun n pn => n + pn.out_nodes.length) (n + m) l
:= by
  intros l n m
  induction l generalizing n m with
  | nil => simp
  | cons pn' l IH =>
    simp [IH]
    congr 1
    omega

theorem find_nb_arcs_cons : ∀ (l : List (PreNode nb_var)) (pn : PreNode nb_var),
  findNbArcs l + pn.out_nodes.length = findNbArcs (pn :: l) :=
by
  intros l pn
  simp [findNbArcs, find_nb_arcs_add]

structure NewAux (nb_var nb_nodes nb_arcs : Nat) (l : List (PreNode nb_var)) : Type where
  nodes : Array (Node nb_var nb_arcs)
  Hnodes : nb_nodes = nodes.size
  arcs : Array (Arc nb_var nb_nodes)
  Harcs : findNbArcs l = arcs.size

def init : NewAux nb_var nb_nodes nb_arcs [] :=
  .mk (Array.replicate nb_nodes (.mk [])) (by simp) #[] rfl

structure StepAux (nb_var nb_nodes nb_arcs : Nat)
  (l : List (PreNode nb_var))
  (out : List (OutNode nb_var)) : Type
where
  nodes : Array (Node nb_var nb_arcs)
  Hnodes : nb_nodes = nodes.size
  arcs : Array (Arc nb_var nb_nodes)
  Harcs : findNbArcs l + out.length = arcs.size

def step.init (l : List (PreNode nb_var))
  (cfg : NewAux nb_var nb_nodes nb_arcs l) :
  StepAux nb_var nb_nodes nb_arcs l []
:= .mk cfg.nodes cfg.Hnodes cfg.arcs cfg.Harcs

def step.aux (l : List (PreNode nb_var)) (i : Fin nb_nodes)
  (out_node : Nat)
  (out_inst : Instruction nb_var)
  (stx : Option (Lean.Syntax))
  (Hout : out_node < nb_nodes)
  (out_nodes : List (OutNode nb_var))
  (Harcs : findNbArcs l + out_nodes.length < nb_arcs)
  (cfg : StepAux nb_var nb_nodes nb_arcs l out_nodes) :
  StepAux nb_var nb_nodes nb_arcs l (⟨out_node, out_inst, stx⟩ :: out_nodes)
:=
  let dst := .mk out_node Hout
  let arc := .mk i dst out_inst stx
  have H : cfg.arcs.size < nb_arcs := by
    rw [← cfg.Harcs]
    assumption
  let arc_idx := .mk cfg.arcs.size H
  let arcs := cfg.arcs.push arc
  have Harcs : findNbArcs l + (⟨out_node, out_inst, stx⟩ :: out_nodes).length = arcs.size := by
    simp [arcs, ← Nat.add_assoc]
    apply cfg.Harcs
  let old_in_arcs := cfg.nodes[cfg.Hnodes ▸ dst].in_nodes
  let new_node := .mk (arc_idx :: old_in_arcs)
  let nodes := cfg.nodes.set dst.1 new_node (cfg.Hnodes ▸ dst.2)
  have Hnodes : nb_nodes = nodes.size := by
    simp [nodes, cfg.Hnodes]
  .mk nodes Hnodes arcs Harcs

def step.run (l : List (PreNode nb_var)) (i : Fin nb_nodes)
  (out_nodes : List (OutNode nb_var))
  (Hn : ∀ p, p ∈ out_nodes → p.out_node < nb_nodes)
  (Harcs : findNbArcs l + out_nodes.length ≤ nb_arcs)
  (cfg : NewAux nb_var nb_nodes nb_arcs l) :
  StepAux nb_var nb_nodes nb_arcs l out_nodes
:= match out_nodes with
| [] => step.init nb_nodes nb_arcs l cfg
| ⟨out_node, out_inst, stx⟩ :: out_nodes =>
  let Hl : findNbArcs l + out_nodes.length ≤ nb_arcs := by
    dsimp at Harcs
    omega
  let cfg := step.run l i out_nodes (by grind) Hl cfg
  step.aux nb_nodes nb_arcs l i out_node out_inst stx (Hn ⟨out_node, out_inst, stx⟩ List.mem_cons_self)
    out_nodes Harcs cfg

def step (l : List (PreNode nb_var))
  (i : Fin nb_nodes) (cfg : NewAux nb_var nb_nodes nb_arcs l)
  (pn : PreNode nb_var) (Hn : pn.id = i ∧
    ∀ p, p ∈ pn.out_nodes → p.out_node < nb_nodes
  )
  (Harcs : findNbArcs l + pn.out_nodes.length ≤ nb_arcs)
  : NewAux nb_var nb_nodes nb_arcs (pn :: l)
:=
  let cfg := step.run nb_nodes nb_arcs l i pn.out_nodes Hn.right Harcs cfg
  let Heq : findNbArcs l + pn.out_nodes.length = findNbArcs (pn :: l) := find_nb_arcs_cons l pn
  .mk cfg.nodes cfg.Hnodes cfg.arcs (Heq ▸ cfg.Harcs)

def aux (l : List (PreNode nb_var))
  (Hlength : List.length l ≤ nb_nodes)
  (Harcs : findNbArcs l ≤ nb_arcs)
  (Hsorted : ∀ i, (l.get i).id = (i + nb_nodes - List.length l) ∧
    ∀ p ∈ (l.get i).out_nodes, p.out_node < nb_nodes)
  : NewAux nb_var nb_nodes nb_arcs l := match l with
| [] => init nb_nodes nb_arcs
| pn :: l =>
  have Ha : findNbArcs l ≤ nb_arcs := by
    dsimp [findNbArcs] at Harcs ⊢
    calc
      _ ≤ _ := by
        apply find_nb_arcs_incr
        apply Nat.zero_le
      _ ≤ _ := Harcs
  have Hl : l.length ≤ nb_nodes := by grind
  let cfg := aux l Hl Ha (by
    intros i
    have : i + nb_nodes - l.length = i.succ + nb_nodes - (pn :: l).length := by
      dsimp
      omega
    simpa [this] using Hsorted i.succ
  )
  let i : Fin nb_nodes := .mk (nb_nodes - List.length (pn :: l)) <| by
    dsimp at Hlength ⊢
    omega
  have Heq : findNbArcs l + pn.out_nodes.length = findNbArcs (pn :: l) := by
    apply find_nb_arcs_cons
  step nb_nodes nb_arcs l i cfg pn (by simpa using Hsorted (0 : Fin (_ + 1)))
    (Heq ▸ Harcs)
end new

def new (l : List (PreNode nb_var)) : Option (Cfg nb_var) :=
  let lsorted := l.mergeSort (fun n₁ n₂ => n₁.id ≤ n₂.id)
  if Hsorted : ∀ i, (lsorted.get i).id = i ∧ ∀ p ∈ (lsorted.get i).out_nodes, p.out_node < lsorted.length then
    let nb_arcs := new.findNbArcs lsorted
    let Hl : l.length = lsorted.length := by
      simp [lsorted]
    let aux := new.aux l.length nb_arcs lsorted (Hl ▸ Nat.le_refl _) (Nat.le_refl _) <| by
      rw [Hl]
      intros i
      rw [Nat.add_sub_cancel]
      apply Hsorted
    .some <| .mk l.length nb_arcs aux.nodes aux.Hnodes aux.arcs (by simp [nb_arcs]; apply aux.Harcs)
  else
    .none

-- TODO: do better
-- true : should widen, false : shouldn't
def getWideningPoints {nb_var : Nat} (cfg : Cfg nb_var) : { arr : Array Bool // arr.size = cfg.nb_nodes }
:=
  let arr := Array.replicate cfg.nb_nodes true
  let Harr : arr.size = cfg.nb_nodes := by
    simp [arr]
  ⟨arr, Harr⟩
end Cfg

structure State (α : Type) [BEq α] [ι : Domain α] (cfg : Cfg ι.nb_var) where
  node_env : Array α -- holds an environment at each node
  Hnode_env : node_env.size = cfg.nb_nodes
  arc_env : Array α -- holds [[arc.inst]](env) for each arc where env is the environment at arc.src
  Harc_env : arc_env.size = cfg.nb_arcs
  widening_points : Array Bool
  Hwidening_points : widening_points.size = cfg.nb_nodes
  nb_step : Nat

namespace State
variable {α : Type} [BEq α] [ι : Domain α] {cfg : Cfg ι.nb_var}

def getNodeEnv (s : State α cfg) (i : Fin cfg.nb_nodes) : α :=
  s.node_env[s.Hnode_env ▸ i]

def setNodeEnv (i : Fin cfg.nb_nodes) (a : α) : StateM (State α cfg) Unit := do
  let s ← get
  let ⟨i,h⟩ := i
  let node_env := s.node_env.set i a (s.Hnode_env ▸ h)
  let Hnode_env : node_env.size = cfg.nb_nodes := by
    rw [←s.Hnode_env]
    simp [node_env]
  set { s with node_env, Hnode_env }

def getArcEnv (s : State α cfg) (i : Fin cfg.nb_arcs) : α :=
  s.arc_env[s.Harc_env ▸ i]

def setArcEnv (i : Fin cfg.nb_arcs) (a : α) : StateM (State α cfg) Unit := do
  let s ← get
  let ⟨i,h⟩ := i
  let arc_env := s.arc_env.set i a (s.Harc_env ▸ h)
  let Harc_env : arc_env.size = cfg.nb_arcs := by
    simp [arc_env, s.Harc_env]
  set { s with arc_env, Harc_env }

def iterArc (arc_idx : Fin cfg.nb_arcs) : StateM (State α cfg) Bool := do
  let s ← get
  let arc := cfg.arcs[cfg.Harcs ▸ arc_idx]
  let src_env := s.getNodeEnv arc.src
  let old_env := s.getArcEnv arc_idx
  let new_env := match arc.inst with
    | .skip => src_env
    | .assign var expr => assign src_env var expr
    | .guard b  => guard src_env b
    | .assert _ => src_env
  setArcEnv arc_idx new_env
  -- this is actually faster than checking just one inclusion:
  --   ¬ (new_env ⊑ old_env)
  -- although, because we always have `old_env ⊑ new_env`, the two
  -- are equivalent
  --
  -- We use BEq to test for inequality, and at the time this was
  -- an important detail. For more information, see
  --     https://github.com/arthur-adjedj/lustrean/pull/5
  return old_env != new_env

def iterNode (node_idx : Fin cfg.nb_nodes) : StateM (State α cfg) Unit := do
  let s ← get
  let node := cfg.nodes[cfg.Hnodes.symm ▸ node_idx]
  let in_env := node.in_nodes.foldl (init := ⊥) fun acc_env arc_idx =>
    let env := s.getArcEnv arc_idx
    acc_env ⊔ env
  let s ← get
  if s.widening_points[s.Hwidening_points ▸ node_idx]
  then
    let old_env := s.getNodeEnv node_idx
    setNodeEnv node_idx (old_env ∇_(s.nb_step) in_env)
  else
    setNodeEnv node_idx in_env

def incrHeartbeat : StateM (State α cfg) Unit := do
  let s ← get
  set { s with nb_step := s.nb_step.succ}

def heartbeat : StateM (State α cfg) Nat := do
  let s ← get
  return s.nb_step

def debug : StateM (State α cfg) Unit := do
  let s ← get
  dbg_trace s!"Step {s.nb_step}"
  for (env, i) in s.node_env.zipIdx do
    dbg_trace s!"  {i}) {env}"

def iter : StateM (State α cfg) Bool := do
  let mut iterate_again := false
  -- debug
  for h : i in [0 :cfg.nb_arcs] do
    let b ← iterArc (.mk' i)
    iterate_again := iterate_again || b
  for h : i in [0 :cfg.nb_nodes] do
    iterNode (.mk' i)
  incrHeartbeat
  return iterate_again

def init : State α cfg :=
  let node_env := Array.replicate cfg.nb_nodes ⊥
  let node_env := if h : 0 < node_env.size then node_env.set 0 ⊤ else node_env
  let Hnode_env : node_env.size = cfg.nb_nodes := by
    rename_i pre_node_env
    dsimp only [node_env]
    split <;> simp [pre_node_env]
  let arc_env := Array.replicate cfg.nb_arcs ⊥
  let Harc_env : arc_env.size = cfg.nb_arcs := by simp [arc_env]
  let ⟨widening_points, Hwidening_points⟩ := cfg.getWideningPoints
  {node_env, Hnode_env, arc_env, Harc_env, widening_points, Hwidening_points, nb_step := 0}

instance : Inhabited (State α cfg) where
  default := init

variable {m : Type → Type} [Monad m]
variable [Lean.MonadLog m] [Lean.AddMessageContext m] [Lean.MonadOptions m]

def checkAssert (s : State α cfg) : m (State α cfg)
:= do
  for h : i in [0 :cfg.nb_arcs] do
    have : i < cfg.arcs.size := Membership.get_elem_helper h cfg.Harcs
    let arc := cfg.arcs[i]
    match arc.inst with
    | .assert b =>
      let old_env := s.getArcEnv ⟨i,cfg.Harcs ▸ this⟩
      let new_env := ι.guard old_env b.not
      if new_env ≠ ⊥
      then
        Lean.logErrorAt? arc.ref? m!"assert failed under {new_env}"
        -- let _ ← Lean.AddErrorMessageContext.add
          -- arc.stx
          -- m!"assert failed, got {old_env}"
    | _ => pure ()
  return s

partial def run (cfg : Cfg ι.nb_var) : m (State α cfg) :=
  (StateT.run loop init).2 |> checkAssert
where
  loop : StateM (State α cfg) Unit := do
    let b ← iter
    if b then loop

end State
end Lustrean