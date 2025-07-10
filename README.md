# IMPORTANT (!!!)

This repository contains the version of FitchVizier that was used during the academic year 2024-2025. As of August 2025, FitchVizier will be maintained by the Fundamental Computing group: [https://github.com/FundamentalComputing/FitchVIZIER](https://github.com/FundamentalComputing/FitchVIZIER). Updates to the tool will only be reflected in FundamentalComputing's repository, not in this one.

# What is this?

This is a formal proof validator, which determines the correctness of Fitch-style natural deduction proofs ("Fitch proofs").

The tool is used by students who follow the course Introduction to Logic (for CS) at the University of Groningen (the Netherlands).

The tool also returns a (hopefully useful) error message in case the proof is not correct.

This application takes Fitch proofs as they are defined in *Language, Proof and Logic*, by Dave Barker-Plummer, Jon Barwise and John Etchemendy.

# How to run it?

It is accessible here: [https://fitch.rug.themisjudge.nl/](https://fitch.rug.themisjudge.nl/) (previously at [https://fitch.themisrug.nl](https://fitch.themisrug.nl)).

If you want to build and run the application locally, then clone the repository, install Cargo if you haven't already and install `wasm-pack` (to compile Rust to WebAssembly) and do:

```
wasm-pack build --target web
```

Once you have it compiled, open a server in the `fitch-proof` directory of the repository:
```
python3 -m http.server 8080
```

And then open [http://localhost:8080/](http://localhost:8080/) in your favorite web browser.
