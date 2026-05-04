(* Axioms used for the proof of the GPU *)
Axiom functional_extensionality : forall {A B} (f g : A -> B),
  (forall x, f x = g x) -> f = g.
