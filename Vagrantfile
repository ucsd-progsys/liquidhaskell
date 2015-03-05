# -*- mode: ruby -*-
# vi: set ft=ruby :

# Vagrantfile API/syntax version. Don't touch unless you know what you're doing!
VAGRANTFILE_API_VERSION = "2"

Vagrant.configure(VAGRANTFILE_API_VERSION) do |config|
  config.vm.provision "shell", inline: "apt-get -y update && apt-get -y install mingw-ocaml"

  config.vm.define "64" do |box|
    box.vm.box = "chef/debian-7.4"
  end
  config.vm.define "32" do |box|
    box.vm.box = "chef/debian-7.4-i386"
  end
end
