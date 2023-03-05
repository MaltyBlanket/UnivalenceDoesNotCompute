In this repository I implement the winding number of the circle as defined in https://dl.acm.org/doi/abs/10.1145/3372885.3373825 by Mörtberg and Pujet in two different proof assistants using two different libraries. 

We define it in Coq using the Coq-HoTT library found in https://github.com/HoTT/Coq-HoTT. There we can see that the function does not compute, because it uses the univalence axiom in its definition. In the end of the file we also prove, that we defined the function in the right way.

We also define it in Agda using the cubical agda library found here: https://github.com/agda/cubical.
There we can see, that the winding number computes, because the univalence axiom is provable in cubical type theory. 

Instructions on how to install Coq and Agda and add the respective libraries, can be found at the respective repository.

This project is part of my bachelor thesis in mathematics at the University of Freiburg supervised by Johan Commelin.
