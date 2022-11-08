doc:
	RUSTDOCFLAGS="--html-in-header doc/katex-header.html" cargo doc --no-deps

.PHONY: doc

# Since the master branch is protected, the current workflow is to create a PR with the version changes,
# and once the PR is merged, run the `make VERSION=<version> release` to publish the new crates.
release:
ifndef VERSION
	$(error VERSION is not set. Run with `make VERSION=<version> release`)
endif
	git pull
	cargo update
	git tag $(VERSION) 
	git push origin $(VERSION)
	cargo release publish --execute --verbose --allow-branch "master"
