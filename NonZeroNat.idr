module NonZeroNat

import MoreNatProofs

%access public export
%default total

data NonZeroNat =
  ||| Unit, aka One
  U |
  ||| Successor
  S NonZeroNat
