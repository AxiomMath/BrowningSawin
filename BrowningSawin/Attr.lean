/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Lean

/-!
# The `browning_sawin` tag attribute

`@[browning_sawin "…"]` records that a declaration formalizes a statement of the source paper, the
string it carries being the label of that statement there. Where one statement of the paper is
formalized by several declarations, each of them carries the tag.
-/

public meta section

open Lean

/-- `@[browning_sawin "TAG"]` records that a declaration formalizes the statement labelled `TAG` in
the source paper. -/
syntax (name := browning_sawin) "browning_sawin " str : attr

initialize Lean.registerBuiltinAttribute {
  name  := `browning_sawin
  descr := "marks a declaration as formalizing the statement with that label in the source paper"
  add   := fun _ _ _ => pure ()
}

end
