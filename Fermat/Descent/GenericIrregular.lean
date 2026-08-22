import Fermat.Descent.GenericIrregular.FixedExponent

/-!
# Generic fixed-exponent irregular-prime assembly

This umbrella module exposes the complete parameterized route

```lean
FixedIrregularCertificate p N → Fermat.HoldsAt p
```

along with all upstream certificate structures imported by
`FixedExponent`.  Concrete exponent adapters remain in their own
directories so dependencies flow from concrete data to generic theory.
-/
