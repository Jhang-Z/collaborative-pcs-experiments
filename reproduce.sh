#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
if ! command -v python3 >/dev/null 2>&1; then
    for argument in "$@"; do
        case "$argument" in
            --check-env|--plan|--no-install|--help|-h)
                echo 'Python 3.10+ is required; this mode does not install missing packages.' >&2
                exit 1
                ;;
        esac
    done
    if command -v apt-get >/dev/null 2>&1; then
        if [ "$(id -u)" -eq 0 ]; then
            apt-get update
            apt-get install --no-install-recommends --no-upgrade -y python3
        else
            sudo apt-get update
            sudo apt-get install --no-install-recommends --no-upgrade -y python3
        fi
    else
        echo 'Python 3.10+ is required; automatic package installation supports Debian/Ubuntu.' >&2
        exit 1
    fi
fi
exec python3 scripts/run.py "$@"
