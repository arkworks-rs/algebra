doc:
	RUSTDOCFLAGS="--html-in-header doc/katex-header.html" cargo doc --no-deps

.PHONY: doc

# Since the master branch is protected, the current workflow is to create a release branch, e.g. `release-0.4` from `master`,
# commit the new version changes, and once the release is done, merge the release branch back to master.
release:
	# Run with `make release VERSION=<version>`
	git checkout master
	git pull
	cargo update
	# run sanity checks
	git tag $(VERSION) 
	git push mmagician $(VERSION)
	# cargo publish
