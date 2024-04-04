# What is this?

Well, it is a Fitch proof verifier!

That is, it verifies the correctness of any inputted Fitch proof, and returns a (hopefully useful) error message in case the proof is not correct. The application aims to support university students who are taking a Logic course, by telling them whether their proof is correct or not, and helping them to make it correct if it isn't.

This application takes Fitch proofs as they are defined in *Language, Proof and Logic*, by Dave Barker-Plummer, Jon Barwise and John Etchemendy.

# How to run it?

Just go to [el-sambal.github.io/fitch-proof](https://el-sambal.github.io/fitch-proof)!

If you want to build and run the application locally, then clone the repository, install Cargo if you haven't already and install `wasm-pack` (to compile Rust to WebAssembly) and do:

```
wasm-pack build --target web
```

Once you have it compiled, open a server in the root directory of the repository:
```
python3 -m http.server 8080
```

And then go [http://localhost:8080/](http://localhost:8080/) in your favorite web browser.
