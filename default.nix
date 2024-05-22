{ sources ? import ./npins
, pkgs ? import sources.nixpkgs {}
, lib ? pkgs.lib
, aeneas-src ? sources.aeneas
, aeneas ? (import aeneas-src {}).packages.x86_64-linux.aeneas
, charon ? (import aeneas-src {}).packages.x86_64-linux.charon
}:
{
  shell = pkgs.mkShell {
    buildInputs = [
      aeneas
      charon
      pkgs.npins
    ];
  };
}
