{
  description = "Idris2 flake";

  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.idris-emacs-src = {
    url = github:redfish64/idris2-mode;
    flake = false;
  };

  outputs = { self, nixpkgs, flake-utils, idris-emacs-src }:
    let idris2-version = "0.3.0";
    in flake-utils.lib.eachDefaultSystem (system:
      let pkgs = import nixpkgs { inherit system; };
          idris2Pkg = pkgs.callPackage ./nix/package.nix { inherit idris2-version; };
          text-editor = import ./nix/text-editor.nix { inherit pkgs idris-emacs-src idris2Pkg; };
          buildIdrisPkg = { projectName, src, idrisLibraries }:
            pkgs.callPackage ./nix/buildIdris.nix
              { inherit src projectName idrisLibraries idris2-version; idris2 = idris2Pkg; };
      in rec {
        packages = rec {
          idris2 = idris2Pkg;
          buildIdris = buildIdrisPkg;
        } // text-editor;
        apps = rec {
          type = "app";
          emacs-dev = text-editor.emacs-dev;
        };
        defaultPackage = packages.idris2;
      }) // rec {
        templates.pkg = {
            path = ./nix/templates/pkg;
            description = "A custom Idris 2 package";
        };
        defaultTemplate = templates.pkg;
        version = idris2-version;
      };
}
