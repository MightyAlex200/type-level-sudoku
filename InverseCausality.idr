module InverseCausality

inverseCausality : ({ a, b : Type } -> (a -> b) -> (b -> a)) -> Void
inverseCausality f = (f (\_ => ())) ()