# Finite certificate layout

This directory groups kernel-checked finite receipts by the part of the FLT
argument they support:

- `CaseI/` contains receipts used to exclude Case I;
- `CaseII_1/` contains the plus-class and principalization receipts;
- `CaseII_2/` contains the lifted-Bernoulli and Vandiver-Lemma-II receipts.

Reusable proof machinery remains in `Fermat/Descent/`, while raw
exponent-specific data and thin adapters may remain in `Fermat/Exponents/`.
Declaration namespaces do not depend on this filesystem classification.
