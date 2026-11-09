module github.com/Giulio2002/Janus/scripts/coverage

go 1.26.0

require (
	github.com/Giulio2002/Janus/validation/hardware-comparison/amd64 v0.0.0
	golang.org/x/arch v0.32.0
)

replace github.com/Giulio2002/Janus/validation/hardware-comparison/amd64 => ../../validation/hardware-comparison/amd64
