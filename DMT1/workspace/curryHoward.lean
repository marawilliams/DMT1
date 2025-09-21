#check And And(a b : Prop) : Prop --takes in 2 propositions and makes single large prop;
--takes in two types and returns a new one
--parametric polymorphic function
#check Prod prod.{u,v} (α : Type u) (β : Type v) : Type (max u v)
--prod is a theorem prover
--product type
-- (α : Type u) (β : Type v) : Type

--defining data type

namespace MyAnd

structure And (a b : Prop) : Prop where
  intro :: --And.intro (similar to struct in C)
  left: a 
  right : b

end MyAnd