{
  description = "Simple rust enviroment";

  inputs = {
    rust-overlay.url = "github:oxalica/rust-overlay";
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, rust-overlay, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (
      system:
        let
          overlays = [ (import rust-overlay) ];
          pkgs = import nixpkgs {
            inherit system overlays;
          };
          nativeBuildInputs = with pkgs; [
            (
              rust-bin.stable.latest.default.override {
                extensions = [ "rust-src" ]; # seems to be already included in stable
              }
            )
          ];
        in
          {
            devShell = with pkgs; mkShell {
              buildInputs = nativeBuildInputs ++ [
                rust-analyzer
                rust-bin.nightly.latest.rustfmt
              ];
            };
          }
    );
}
