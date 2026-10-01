#!/usr/bin/env bash

# Compile and serve the web version of the blueprint.

set -euo pipefail

lake build :blueprint

uvx leanblueprint web
uvx leanblueprint serve
