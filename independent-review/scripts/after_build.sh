#!/usr/bin/env bash
# Sequential post-build work: README verification commands + own audits, then committee stages.
/path/to/ym-release/review/scripts/post_build.sh
/path/to/ym-release/review/scripts/committee_stages.sh
echo "AFTER_BUILD_DONE $(date -Is)"
