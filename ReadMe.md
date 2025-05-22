# KBO Systems

- slothrop (2006)
    - https://homepage.divms.uiowa.edu/~astump/papers/rta06.pdf
    - (longer thesis) https://cs.bc.edu/~stumpaa/papers/thesis-wehrman.pdf
    - https://github.com/iwehrman/Slothrop
    - KBC extension without ordering, uses aprover to prove termination
    - takes long but is powerful
- maxcomp (2011)
    - https://drops.dagstuhl.de/storage/00lipics/lipics-vol010-rta2011/LIPIcs.RTA.2011.71/LIPIcs.RTA.2011.71.pdf
    - http://www.jaist.ac.jp/project/maxcomp/
    - Improvement (integrated): (2021)
        - https://drops.dagstuhl.de/storage/00lipics/lipics-vol195-fscd2021/LIPIcs.FSCD.2021.2/LIPIcs.FSCD.2021.2.pdf
    - MaxCompDP (2015)
        - http://cl-informatik.uibk.ac.at/users/swinkler/bolzano/papers/SW15.pdf
- twee (2021)
    - https://github.com/nick8325/twee
    - https://link.springer.com/chapter/10.1007/978-3-030-79876-5_35
    - Theorem prover
    - uses normal kbc with fixed order
- waldmeister
- kbcv
    - http://cl-informatik.uibk.ac.at/users/hzankl/new/publications/ST12_02.pdf
    - http://cl-informatik.uibk.ac.at/software/kbcv/
    - interactive and automatic mode
    - claims to be competitive with maxcomp, slothrop, MKBTT
    - kbcv2 (2015)
        - https://arxiv.org/pdf/1505.01338
        - performance improvements
mkbtt (2008, 2009, 2010)
    - http://cl-informatik.uibk.ac.at/software/mkbtt/


# EGraph Systems

- egg (2021)
    - https://github.com/egraphs-good/egg
    - https://dl.acm.org/doi/10.1145/3434304
- egglog (2023)
    - https://github.com/egraphs-good/egglog
    - https://dl.acm.org/doi/10.1145/3591239




# Compare EGraphs and Knuth-Bendix


- egraphs:
    - good:
        - common subexpression
    - bad:
        - equations that blow up
        - undirected
- knuth bendix:
    - good:
        - static
        - easy to apply
    - bad:
        - can fail to complete
        - not always orientable