{
  description = "ocpl-coq development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/release-25.11";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            coq_8_9
            python3
            gnumake
            gcc
            git
            m4
            pkg-config
          ];

          shellHook = ''
            echo "ocpl-coq development environment"
            coqc --version
          '';
        };
      }
    );
}
