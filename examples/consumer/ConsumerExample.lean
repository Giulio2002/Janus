-- The library root: the extraction-independent modules, which `lake build` builds.
-- Theorem modules (ConsumerExample.Add, ConsumerExample.Max) import `Extracted`, which
-- `janus verify` supplies from an artifact directory; they are not imported here.
import ConsumerExample.Spec
