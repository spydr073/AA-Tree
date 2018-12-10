{ build-idris-package
, prelude
, base
, lib
, idris
}:

build-idris-package {
  name    = "aatree";
  version = "0.1";
  src = ./.;

  #buildDepends = [];
  #idrisDeps = [ effects ];
  propagatedBuildInputs = [ prelude base ];

  meta = {
    description = "";
    license = "";
    maintainers = "";
  };

}


