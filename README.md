# Type Inference Zoo

![Build Status](https://github.com/cu1ch3n/type-inference-zoo/actions/workflows/build.yml/badge.svg)
![License](https://img.shields.io/badge/license-MIT-blue.svg)


Welcome to **Type Inference Zoo**! This project is dedicated to implementing a variety of type inference algorithms. It serves as a personal project, as I am trying to understand the type inference algorithms well by implmenting them. Considering that it might be helpful for those who are also exploring type inference algoreithms, I am glad to make them avaliable online.

🗿🗿🗿 There are indeed animals (**implementations**) in the zoo, not only references to animals.

A static online web demo is available for you to try at https://zoo.cuichen.cc/.

## 🚀 Get Started

To get started with the project, clone the repository and build the project using [`stack`](https://docs.haskellstack.org/):

```bash
git clone https://github.com/cu1ch3n/type-inference-zoo.git
cd type-inference-zoo
stack build
stack exec type-inference-zoo-exe -- "let id = \x. x in (id 1, id True)" --alg W
```

## Research Works Implemented

- [x] `W`: [`./src/Alg/HDM/AlgW.hs`](./src/Alg/HDM/AlgW.hs)
  - *Robin Milner.* **A Theory of Type Polymorphism in Programming.** Journal of Computer and System Sciences, 1978.
    [[Paper](https://www.sciencedirect.com/science/article/pii/0022000078900144)]
- [x] `DK`: [`./src/Alg/DK/DK.hs`](./src/Alg/DK/DK.hs)
  - *Jana Dunfield and Neelakantan R. Krishnaswami.* **Complete and Easy Bidirectional Typechecking for Higher-rank Polymorphism.** ICFP 2013. 
    [[Paper](https://dl.acm.org/doi/10.1145/2500365.2500582)]
- [x] `Worklist`: [`./src/Alg/DK/Worklist/DK.hs`](./src/Alg/DK/Worklist/DK.hs)
  - *Jinxu Zhao, Bruno C. d. S. Oliveira, and Tom Schrijvers.* **A Mechanical Formalization of Higher-Ranked Polymorphic Type Inference.** ICFP 2019.
    [[Paper](https://dl.acm.org/doi/10.1145/3341716)]
- [x] `Elementary`: [`./src/Alg/DK/Worklist/Elementary.hs`](./src/Alg/DK/Worklist/Elementary.hs)
  - *Jinxu Zhao and Bruno C. d. S. Oliveira.* **Elementary Type Inference.** ECOOP 2022.
    [[Paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2022.2)]
- [x] `R`: [`./src/Alg/HDM/AlgR.hs`](./src/Alg/HDM/AlgR.hs)
  - *Roger Bosman, Georgios Karachalias, Tom Schrijvers.* **No Unification Variable Left Behind: Fully Grounding Type Inference for the HDM System.** ITP 2023.
- [x] `Bounded`: [`./src/Alg/DK/Worklist/Bounded.hs`](./src/Alg/DK/Worklist/Bounded.hs)
  - *Chen Cui, Shengyi Jiang, and Bruno C. d. S. Oliveira.* **Greedy Implicit Bounded Quantification.** OOPSLA 2023.
    [[Paper](https://dl.acm.org/doi/10.1145/3622871)]
- [x] `Contextual`: [`./src/Alg/Local/Contextual/Contextual.hs`](./src/Alg/Local/Contextual/Contextual.hs)
  - *Xu Xue and Bruno C. d. S. Oliveira.* **Contextual Typing.** ICFP 2024.
    [[Paper](https://dl.acm.org/doi/10.1145/3674655)]
- [x] `IU`: [`./src/Alg/DK/Worklist/IU.hs`](./src/Alg/DK/Worklist/IU.hs)
  - *Shengyi Jiang, Chen Cui and Bruno C. d. S. Oliveira.* **Bidirectional Higher-Rank Polymorphism with Intersection and Union Types.** POPL 2025.
    [[Paper](https://i.cs.hku.hk/~bruno/papers/popl25_hrp.pdf)]

## Contribution

Contributions are welcome! If you're interested in improving this project, please feel free to open an issue or submit a pull request.

## License

This project is licensed under the MIT License.

## Disclaim

This project is still in its early stages, and I am not an expert in either type inference or Haskell :) Please use it at your own risk (Some of the code was assisted by GitHub Copilot or ChatGPT). If you spot any issues or have suggestions, please open an issue to help improve the project.