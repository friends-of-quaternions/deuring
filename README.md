# Constructive Deuring Correspondence in SageMath

Code accompanying the research paper
[*Deuring for the People: Supersingular Elliptic Curves with Prescribed Endomorphism Ring in General Characteristic*](//ia.cr/2023/106)
by Jonathan Komada Eriksen, Lorenz Panny, Jana Sotáková, and Mattia Veroni.

Usage example:
```sage
sage: from deuring.broker import starting_curve
sage: from deuring.randomideal import random_ideal
sage: from deuring.correspondence import constructive_deuring
sage: F2.<i> = GF((2^31-1, 2), modulus=[1,0,1])
sage: E0, iota, O0 = starting_curve(F2)
sage: I = random_ideal(O0)
sage: I
Fractional ideal (-2227737332 - 2733458099/2*i - 36405/2*j + 7076*k, -1722016565/2 + 1401001825/2*i + 551/2*j + 16579/2*k, -2147483647 - 9708*j + 12777*k, -2147483647 - 2147483647*i - 22485*j + 3069*k)
sage: E1, phi, _ = constructive_deuring(I, E0, iota)
sage: phi
Composite morphism of degree 14763897348161206530374369280 = 2^29*3^3*5*7^2*11*13*17*31*41*43^2*61*79*151:
  From: Elliptic Curve defined by y^2 = x^3 + x over Finite Field in i of size 2147483647^2
  To:   Elliptic Curve defined by y^2 = x^3 + (1474953432*i+1816867654)*x + (581679615*i+260136654) over Finite Field in i of size 2147483647^2
```

