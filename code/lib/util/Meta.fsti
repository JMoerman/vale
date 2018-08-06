module Meta

val generic_injective_proof : #a:eqtype -> #b:eqtype -> f:(a->b) -> g:(b->a) -> l:(x:a -> Lemma (g (f x) == x))
  -> Lemma (forall (x x':a) . f x == f x' ==> x == x')

val exists_elim2 (goal:Type) (#a:Type) (#b:(a -> Type))  (#p:(x:a -> b x -> Type))
                 (_:squash (exists (x:a) (y:b x). p x y))
                 (f:(x:a -> y:b x{p x y} -> GTot (squash goal))) :Lemma goal
