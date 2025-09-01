/- @@@
# Counterexamples

<!-- toc -->
@@@ -/

import DMT1.L03_modelTheory.models

namespace DMT1.L03_modelTheory.counterexamples

open DMT1.L02_propLogic.syntax
open DMT1.L02_propLogic.semantics
open DMT1.L03_modelTheory.models

/- @@@

## Final All Counterexamples
A counterexample is an interpretation that makes a proposition
false. If you write a *specification*, S, about a system in the
form of a proposition that should be true of all possible system
behaviors, you'd like to know if there are any behaviors that
do *not* satisfy the specification. Such a behavior would be
a *counterexample* to the specification. So how might we put
together a method for finding a counterexample if there is one?
@@@ -/

def findCounterexamples (e : Expr) : List Interp := findModels ¬e


/- @@@
## Find One Counterexample
@@@ -/

def findCounterexample (e : Expr) : Option Interp := findModel ¬e

/- @@@
These functions use types you don't yet know about: namely List and Option.
You should understand lists intuitively from CS1. You can think of an option
as a list of length either zero (called none) or one (called some e), where
e the specific value in the length-one list of values (an interpertation).
@@@ -/

end DMT1.L03_modelTheory.counterexamples
