{
  description = "My Idris 2 package";

  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.idris = {
    url = github:idris-lang/Idris2;
    inputs.flake-utils.follows = "flake-utils";
  };

  outputs = { self, idris, flake-utils }: flake-utils.lib.eachDefaultSystem (system:
    let
      idrisPkgs = idris.packages.${system};
      pkgs = idrisPkgs.buildIdris {
        projectName = "mypkg";
        src = ./.;
        idrisLibraries = [];
      };
    in rec {
      packages = pkgs // idrisPkgs;
      defaultPackage = pkgs.build;
    }
  );
}
