def andAssoc : Prop := ∀ (P Q R : Prop), P ∧ (Q ∧ R) → (P ∧ Q) ∧ R

--my answer
def pfAndAssoc1 : andAssoc :=
    fun (P Q R : Prop) =>  --assume PQR are propositions
        (
          fun (h : P ∧ (Q ∧ R)) =>
          (
                let p := h.left
                let q := h.right.left
                let r := h.right.right
                let pq := And.intro p q
                And.intro pq r
          )
            --place holder for proof
        -- below we need a proof of? look at lean InfoView to find what is left needed
        --P ∧ Q ∧ R → (P ∧ Q) ∧ R how does this break apart? at the implication arrow (top level symbol)
        --order of operations! is why → is top level
        --assume you have a proof of the left
        )

--answer from professor

def pfAndAssoc : andAssoc :=
    fun (P Q R : Prop) =>  --assume PQR are propositions
        (
          fun (pqr : P ∧ (Q ∧ R)) =>
          (
            let p : P := pqr.left
            let q: Q := pqr.right.left
            let r: R := pqr.right.right
            let pq : P ∧ Q := And.intro p q
            And.intro pq r
          )
            --place holder for proof
        -- below we need a proof of? look at lean InfoView to find what is left needed
        --P ∧ Q ∧ R → (P ∧ Q) ∧ R how does this break apart? at the implication arrow (top level symbol)
        --order of operations! is why → is top level
        --assume you have a proof of the left
        )
